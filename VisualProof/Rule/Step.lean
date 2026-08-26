import VisualProof.Rule.WireSever
import VisualProof.Rule.Iteration
import VisualProof.Rule.DoubleCut
import VisualProof.Rule.Vacuity
import VisualProof.Rule.Presentation
import VisualProof.Rule.Identification
import VisualProof.Rule.Lambda
import VisualProof.Rule.WirePrimitive

namespace VisualProof.Rule

open Diagram
open Theory

/-- The authoritative proof-relevant inventory of primitive one-step rules. -/
inductive Step.Evidence {boundary : List Sig} :
    OpenDiagram boundary → OpenDiagram boundary → Type
  | wireSever : WireSever source target → Evidence source target
  | iteration : Iteration source target → Evidence source target
  | doubleCut : DoubleCut source target → Evidence source target
  | vacuity : Vacuity source target → Evidence source target
  | presentation : Presentation source target → Evidence source target
  | identification : Identification source target → Evidence source target
  | cutShape : WirePrimitive.CutShape source target → Evidence source target
  | parallelShape : WirePrimitive.ParallelShape source target →
      Evidence source target
  | ends : WirePrimitive.Ends source target → Evidence source target
  | arity : WirePrimitive.Arity source target → Evidence source target
  | argumentPermutation : WirePrimitive.ArgumentPermutation source target →
      Evidence source target
  | argumentDuplicate : WirePrimitive.ArgumentDuplicate source target →
      Evidence source target
  | argumentProjection : WirePrimitive.ArgumentProjection source target →
      Evidence source target
  | formalApplication : WirePrimitive.FormalApplication source target →
      Evidence source target
  | identityLeaf : WirePrimitive.IdentityLeaf source target →
      Evidence source target
  | lambdaSpawn : Lambda.Spawn source target → Evidence source target
  | lambdaTermLeaf : Lambda.TermLeaf source target → Evidence source target

/-- The relational view of the proof-relevant one-step evidence. -/
def Step {boundary : List Sig}
    (source target : OpenDiagram boundary) : Prop :=
  Nonempty (Step.Evidence source target)

namespace Step

def wireSever (step : WireSever source target) : Step source target :=
  ⟨.wireSever step⟩

def iteration (step : Iteration source target) : Step source target :=
  ⟨.iteration step⟩

def doubleCut (step : DoubleCut source target) : Step source target :=
  ⟨.doubleCut step⟩

def vacuity (step : Vacuity source target) : Step source target :=
  ⟨.vacuity step⟩

def presentation (step : Presentation source target) : Step source target :=
  ⟨.presentation step⟩

def identification (step : Identification source target) : Step source target :=
  ⟨.identification step⟩

def cutShape (step : WirePrimitive.CutShape source target) : Step source target :=
  ⟨.cutShape step⟩

def parallelShape (step : WirePrimitive.ParallelShape source target) :
    Step source target :=
  ⟨.parallelShape step⟩

def ends (step : WirePrimitive.Ends source target) : Step source target :=
  ⟨.ends step⟩

def arity (step : WirePrimitive.Arity source target) : Step source target :=
  ⟨.arity step⟩

def argumentPermutation
    (step : WirePrimitive.ArgumentPermutation source target) : Step source target :=
  ⟨.argumentPermutation step⟩

def argumentDuplicate
    (step : WirePrimitive.ArgumentDuplicate source target) : Step source target :=
  ⟨.argumentDuplicate step⟩

def argumentProjection
    (step : WirePrimitive.ArgumentProjection source target) : Step source target :=
  ⟨.argumentProjection step⟩

def formalApplication
    (step : WirePrimitive.FormalApplication source target) : Step source target :=
  ⟨.formalApplication step⟩

def identityLeaf
    (step : WirePrimitive.IdentityLeaf source target) : Step source target :=
  ⟨.identityLeaf step⟩

def lambdaSpawn (step : Lambda.Spawn source target) : Step source target :=
  ⟨.lambdaSpawn step⟩

def lambdaTermLeaf (step : Lambda.TermLeaf source target) : Step source target :=
  ⟨.lambdaTermLeaf step⟩

def Evidence.iso
    {boundary : List Sig}
    {source source' target target' : OpenDiagram boundary}
    (sourceIso : OpenDiagramIso source source')
    (evidence : Evidence source target)
    (targetIso : OpenDiagramIso target target') :
    Evidence source' target' := by
  cases evidence with
  | wireSever step =>
      exact .wireSever (WireSever.iso sourceIso step targetIso)
  | iteration step =>
      exact .iteration (Iteration.iso sourceIso step targetIso)
  | doubleCut step =>
      exact .doubleCut (DoubleCut.iso sourceIso step targetIso)
  | vacuity step =>
      exact .vacuity (Vacuity.iso sourceIso step targetIso)
  | presentation step =>
      exact .presentation (Presentation.iso sourceIso step targetIso)
  | identification step =>
      exact .identification (Identification.iso sourceIso step targetIso)
  | cutShape step =>
      exact .cutShape (WirePrimitive.CutShape.iso sourceIso step targetIso)
  | parallelShape step =>
      exact .parallelShape
        (WirePrimitive.ParallelShape.iso sourceIso step targetIso)
  | ends step =>
      exact .ends (WirePrimitive.Ends.iso sourceIso step targetIso)
  | arity step =>
      exact .arity (WirePrimitive.Arity.iso sourceIso step targetIso)
  | argumentPermutation step =>
      exact .argumentPermutation
        (WirePrimitive.ArgumentPermutation.iso sourceIso step targetIso)
  | argumentDuplicate step =>
      exact .argumentDuplicate
        (WirePrimitive.ArgumentDuplicate.iso sourceIso step targetIso)
  | argumentProjection step =>
      exact .argumentProjection
        (WirePrimitive.ArgumentProjection.iso sourceIso step targetIso)
  | formalApplication step =>
      exact .formalApplication
        (WirePrimitive.FormalApplication.iso sourceIso step targetIso)
  | identityLeaf step =>
      exact .identityLeaf
        (WirePrimitive.IdentityLeaf.iso sourceIso step targetIso)
  | lambdaSpawn step =>
      exact .lambdaSpawn (Lambda.Spawn.iso sourceIso step targetIso)
  | lambdaTermLeaf step =>
      exact .lambdaTermLeaf (Lambda.TermLeaf.iso sourceIso step targetIso)

theorem iso
    {boundary : List Sig}
    {source source' target target' : OpenDiagram boundary}
    (sourceIso : OpenDiagramIso source source')
    (step : Step source target)
    (targetIso : OpenDiagramIso target target') :
    Step source' target' := by
  rcases step with ⟨evidence⟩
  exact ⟨Evidence.iso sourceIso evidence targetIso⟩

end Step

end VisualProof.Rule
