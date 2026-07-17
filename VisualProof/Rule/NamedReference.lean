import VisualProof.Theory.Semantics
import VisualProof.Diagram.Concrete.Subgraph.Splice

namespace VisualProof.Rule

open VisualProof
open VisualProof.Data.Finite
open Diagram

/-- The canonical open diagram denoting one named relation applied to its
ordered boundary arguments. -/
def namedReferencePatternRaw (signature : List Nat)
    (definition : Fin signature.length) : OpenConcreteDiagram where
  diagram := {
    regionCount := 1
    nodeCount := 1
    wireCount := signature.get definition
    root := 0
    regions := fun _ => .sheet
    nodes := fun _ => .named 0 definition.val (signature.get definition)
    wires := fun wire => {
      scope := 0
      endpoints := [{ node := 0, port := .arg wire }]
    }
  }
  boundary := allFin (signature.get definition)

theorem namedReferencePatternRaw_wellFormed
    (signature : List Nat) (definition : Fin signature.length) :
    (namedReferencePatternRaw signature definition).WellFormed signature := by
  constructor
  · constructor
    · rfl
    · intro region _
      change Fin 1 at region
      change region = (0 : Fin 1)
      exact Subsingleton.elim _ _
    · intro region
      change Fin 1 at region
      have hregion : region = (0 : Fin 1) := Subsingleton.elim _ _
      subst region
      exact ConcreteDiagram.Encloses.refl _ _
    · intro node
      trivial
    · intro node
      trivial
    · intro node
      change signature[definition.val]? = some (signature.get definition)
      simpa [List.get_eq_getElem] using
        List.getElem?_eq_getElem definition.isLt
    · intro wire endpoint hendpoint
      change Fin (signature.get definition) at wire
      change CEndpoint 1 at endpoint
      have heq : endpoint = { node := 0, port := .arg wire } := by
        exact List.mem_singleton.mp hendpoint
      rw [heq]
      exact ⟨wire, rfl⟩
    · intro wire
      simp [namedReferencePatternRaw]
    · intro left right hne endpoint hleft
      change Fin (signature.get definition) at left right
      change CEndpoint 1 at endpoint
      have heq : endpoint = { node := 0, port := .arg left } := by
        exact List.mem_singleton.mp hleft
      rw [heq]
      change (!decide
        (({ node := 0, port := CPort.arg left } : CEndpoint 1) ∈
          [{ node := 0, port := CPort.arg right }])) = true
      have hnot :
          ¬(({ node := 0, port := CPort.arg left } : CEndpoint 1) ∈
            [{ node := 0, port := CPort.arg right }]) := by
        intro hright
        have endpointEq := List.mem_singleton.mp hright
        apply bne_iff_ne.mp hne
        apply Fin.ext
        simpa using congrArg
          (fun endpoint : CEndpoint 1 => endpoint.port) endpointEq
      simp [hnot]
    · intro node index
      change Fin 1 at node
      refine ⟨index, ?_⟩
      change ({ node := node, port := CPort.arg index } : CEndpoint 1) ∈
        [{ node := 0, port := CPort.arg index }]
      simp only [List.mem_singleton]
      congr
      exact Subsingleton.elim _ _
    · intro wire endpoint hendpoint
      simpa [namedReferencePatternRaw] using
        (ConcreteDiagram.Encloses.refl
          (namedReferencePatternRaw signature definition).diagram
          (0 : Fin 1))
  · intro wire _
    rfl

def namedReferencePattern (signature : List Nat)
    (definition : Fin signature.length) : CheckedOpenDiagram signature :=
  ⟨namedReferencePatternRaw signature definition,
    namedReferencePatternRaw_wellFormed signature definition⟩

theorem namedReferencePattern_boundary_length
    (signature : List Nat) (definition : Fin signature.length) :
    (namedReferencePatternRaw signature definition).boundary.length =
      signature.get definition := by
  simp [namedReferencePatternRaw, allFin_eq_finRange]

end VisualProof.Rule
