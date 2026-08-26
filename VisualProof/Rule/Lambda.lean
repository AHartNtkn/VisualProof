import VisualProof.Rule.Lambda.Spawn
import VisualProof.Rule.Lambda.TermLeaf
import VisualProof.Lambda.Reduction

namespace VisualProof.Rule.Lambda

open Diagram
open Theory

namespace Conversion

/-- The common positional carrier through which the source and replacement
free-slot interfaces are compared. Every carrier position is owned by at least
one side. -/
structure Correspondence (leftArity rightArity : Nat) where
  commonArity : Nat
  left : Fin leftArity → Fin commonArity
  right : Fin rightArity → Fin commonArity
  covered : ∀ commonSlot,
    (∃ leftSlot, left leftSlot = commonSlot) ∨
      (∃ rightSlot, right rightSlot = commonSlot)

def Correspondence.symm
    (correspondence : Correspondence leftArity rightArity) :
    Correspondence rightArity leftArity where
  commonArity := correspondence.commonArity
  left := correspondence.right
  right := correspondence.left
  covered := fun commonSlot =>
    (correspondence.covered commonSlot).elim Or.inr Or.inl

/-- One exact term-node replacement. The host output is preserved, while both
free-slot interfaces are quotiented through the same covered positional carrier. -/
structure Description (wires : List Sig) where
  leftArity : Nat
  rightArity : Nat
  leftTerm : VisualProof.Lambda.Term 0 (Fin leftArity)
  rightTerm : VisualProof.Lambda.Term 0 (Fin rightArity)
  correspondence : Correspondence leftArity rightArity
  output : Var wires .iota
  carrier : Fin correspondence.commonArity → Var wires .iota
  betaEta : VisualProof.Lambda.BetaEta
    (leftTerm.mapFree correspondence.left)
    (rightTerm.mapFree correspondence.right)

def Description.source (description : Description wires) : Region wires :=
  Region.singleton (.term description.output description.leftArity
    (fun slot => description.carrier (description.correspondence.left slot))
    description.leftTerm)

def Description.target (description : Description wires) : Region wires :=
  Region.singleton (.term description.output description.rightArity
    (fun slot => description.carrier (description.correspondence.right slot))
    description.rightTerm)

def Description.symm (description : Description wires) : Description wires where
  leftArity := description.rightArity
  rightArity := description.leftArity
  leftTerm := description.rightTerm
  rightTerm := description.leftTerm
  correspondence := description.correspondence.symm
  output := description.output
  carrier := description.carrier
  betaEta := description.betaEta.symm

@[simp] theorem Description.symm_source
    (description : Description wires) :
    description.symm.source = description.target := rfl

@[simp] theorem Description.symm_target
    (description : Description wires) :
    description.symm.target = description.source := rfl

inductive Local : LocalRule
  | convert (description : Description wires) :
      Local description.source description.target

theorem Local.symm {before after : Region wires}
    (step : Local before after) : Local after before := by
  cases step with
  | convert description =>
      simpa using Local.convert description.symm

end Conversion

/-- Replace one whole term by a beta-eta-equivalent term at an exact diagram
occurrence. -/
def Conversion : Rule := Contextual Conversion.Local

theorem Conversion.iso
    (sourceIso : OpenDiagramIso source source')
    (step : Conversion source target)
    (targetIso : OpenDiagramIso target target') :
    Conversion source' target' :=
  Contextual.iso sourceIso step targetIso

theorem Conversion.symm
    (step : Conversion source target) : Conversion target source := by
  rcases step with ⟨wires, before, after, occurrence, targetCanonical,
    targetExternalTwoEnded, targetIso, localEvidence⟩
  let reverseOccurrence : Occurrence after target := {
    interface := occurrence.interface
    context := occurrence.context
    sourceCanonical := targetCanonical
    sourceExternalTwoEnded := targetExternalTwoEnded
    host_iso := targetIso
  }
  refine ⟨wires, after, before, reverseOccurrence,
    occurrence.sourceCanonical, occurrence.sourceExternalTwoEnded,
    occurrence.host_iso, ?_⟩
  cases polarity : occurrence.context.polarity <;>
    simp only [polarity, atPolarity, converse] at localEvidence ⊢
  · exact localEvidence.symm
  · exact localEvidence.symm

namespace FreeVariableIdentity

def otherPosition : Fin 2 → Fin 2 :=
  Fin.cases 1 (fun _ => 0)

/-- A binary identity together with the incidence selected as the term output.
The opposite incidence becomes free slot zero. -/
structure Description (wires : List Sig) where
  ports : Fin 2 → Var wires .iota
  outputPosition : Fin 2

def Description.output (description : Description wires) : Var wires .iota :=
  description.ports description.outputPosition

def Description.input (description : Description wires) : Var wires .iota :=
  description.ports (otherPosition description.outputPosition)

def Description.term (description : Description wires) : Region wires :=
  Region.singleton (.term description.output 1 (fun _ => description.input)
    (.port 0))

def Description.identity (description : Description wires) : Region wires :=
  Region.singleton (.identity .iota 2 description.ports)

inductive Local : LocalRule
  | toIdentity (description : Description wires) :
      Local description.term description.identity
  | toTerm (description : Description wires) :
      Local description.identity description.term

theorem Local.symm {before after : Region wires}
    (step : Local before after) : Local after before := by
  cases step with
  | toIdentity description => exact .toTerm description
  | toTerm description => exact .toIdentity description

end FreeVariableIdentity

/-- Convert exactly `term output 1 ports (.port 0)` to a binary individual
identity, or choose either identity incidence as the output in the converse. -/
def FreeVariableIdentity : Rule := Contextual FreeVariableIdentity.Local

theorem FreeVariableIdentity.iso
    (sourceIso : OpenDiagramIso source source')
    (step : FreeVariableIdentity source target)
    (targetIso : OpenDiagramIso target target') :
    FreeVariableIdentity source' target' :=
  Contextual.iso sourceIso step targetIso

theorem FreeVariableIdentity.symm
    (step : FreeVariableIdentity source target) :
    FreeVariableIdentity target source := by
  rcases step with ⟨wires, before, after, occurrence, targetCanonical,
    targetExternalTwoEnded, targetIso, localEvidence⟩
  let reverseOccurrence : Occurrence after target := {
    interface := occurrence.interface
    context := occurrence.context
    sourceCanonical := targetCanonical
    sourceExternalTwoEnded := targetExternalTwoEnded
    host_iso := targetIso
  }
  refine ⟨wires, after, before, reverseOccurrence,
    occurrence.sourceCanonical, occurrence.sourceExternalTwoEnded,
    occurrence.host_iso, ?_⟩
  cases polarity : occurrence.context.polarity <;>
    simp only [polarity, atPolarity, converse] at localEvidence ⊢
  · exact localEvidence.symm
  · exact localEvidence.symm

end VisualProof.Rule.Lambda
