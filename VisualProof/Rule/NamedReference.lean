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

/-- The concrete identity quotient carried by a named-reference occurrence.
Every argument position selects one concrete wire, and surjectivity rules out
irrelevant empty wires. Distinct argument positions may select the same wire. -/
structure NamedReferenceWiring (arity : Nat) where
  wireCount : Nat
  argumentWire : Fin arity → Fin wireCount
  argumentWire_surjective : Function.Surjective argumentWire

/-- A named-reference node whose ordered argument interface realizes an
arbitrary concrete identity quotient. The ordinary canonical reference is the
special case in which `argumentWire` is the identity. -/
def wiredNamedReferencePatternRaw (signature : List Nat)
    (definition : Fin signature.length)
    (wiring : NamedReferenceWiring (signature.get definition)) :
    OpenConcreteDiagram where
  diagram := {
    regionCount := 1
    nodeCount := 1
    wireCount := wiring.wireCount
    root := 0
    regions := fun _ => .sheet
    nodes := fun _ =>
      .named 0 definition.val (signature.get definition)
    wires := fun wire => {
      scope := 0
      endpoints := (allFin (signature.get definition)).filterMap fun argument =>
        if wiring.argumentWire argument = wire then
          some { node := 0, port := .arg argument }
        else none
    }
  }
  boundary := List.ofFn wiring.argumentWire

/-- Arbitrary argument-wire quotients preserve the concrete well-formedness of
one named-reference node. -/
theorem wiredNamedReferencePatternRaw_wellFormed
    (signature : List Nat) (definition : Fin signature.length)
    (wiring : NamedReferenceWiring (signature.get definition)) :
    (wiredNamedReferencePatternRaw signature definition wiring).WellFormed
      signature := by
  constructor
  · constructor
    · rfl
    · intro region _
      change region = (0 : Fin 1)
      exact Subsingleton.elim (α := Fin 1) region 0
    · intro region
      change Fin 1 at region
      have regionEq : region = (0 : Fin 1) := Subsingleton.elim _ _
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
    · intro wire endpoint endpointMember
      change CEndpoint 1 at endpoint
      obtain ⟨argument, _, mapped⟩ := List.mem_filterMap.mp endpointMember
      have wireEq : wiring.argumentWire argument = wire := by
        by_cases equal : wiring.argumentWire argument = wire
        · exact equal
        · have impossible : False := by simpa [equal] using mapped
          exact impossible.elim
      have endpointEq : endpoint =
          ({ node := 0, port := CPort.arg argument } : CEndpoint 1) := by
        have simplified := mapped
        rw [if_pos wireEq] at simplified
        exact (Option.some.inj simplified).symm
      rw [endpointEq]
      change ∃ index : Fin (signature.get definition),
        CPort.arg argument = CPort.arg index
      exact ⟨argument, rfl⟩
    · intro wire
      apply List.Pairwise.filterMap
        (R := fun left right : Fin (signature.get definition) => left ≠ right)
        (S := (· ≠ ·))
      · intro left right different leftEndpoint leftMapped rightEndpoint
          rightMapped endpointEq
        change CEndpoint 1 at leftEndpoint rightEndpoint
        have leftWireEq : wiring.argumentWire left = wire := by
          by_cases equal : wiring.argumentWire left = wire
          · exact equal
          · have impossible : False := by simpa [equal] using leftMapped
            exact impossible.elim
        have rightWireEq : wiring.argumentWire right = wire := by
          by_cases equal : wiring.argumentWire right = wire
          · exact equal
          · have impossible : False := by simpa [equal] using rightMapped
            exact impossible.elim
        have leftEq : leftEndpoint =
            ({ node := 0, port := CPort.arg left } : CEndpoint 1) := by
          have simplified := leftMapped
          rw [if_pos leftWireEq] at simplified
          exact (Option.some.inj simplified).symm
        have rightEq : rightEndpoint =
            ({ node := 0, port := CPort.arg right } : CEndpoint 1) := by
          have simplified := rightMapped
          rw [if_pos rightWireEq] at simplified
          exact (Option.some.inj simplified).symm
        rw [leftEq, rightEq] at endpointEq
        apply different
        apply Fin.ext
        simpa using congrArg
          (fun endpoint : CEndpoint 1 => endpoint.port) endpointEq
      · exact allFin_nodup (signature.get definition)
    · intro left right different endpoint leftMember
      change CEndpoint 1 at endpoint
      obtain ⟨leftArgument, _, leftMapped⟩ :=
        List.mem_filterMap.mp leftMember
      have leftWireEq : wiring.argumentWire leftArgument = left := by
        by_cases equal : wiring.argumentWire leftArgument = left
        · exact equal
        · have impossible : False := by simpa [equal] using leftMapped
          exact impossible.elim
      have leftEndpointEq :
          ({ node := 0, port := CPort.arg leftArgument } : CEndpoint 1) =
            endpoint := by
        have simplified := leftMapped
        rw [if_pos leftWireEq] at simplified
        exact Option.some.inj simplified
      unfold ConcreteDiagram.EndpointOccurs
      change (!decide (endpoint ∈
        (allFin (signature.get definition)).filterMap fun argument =>
          if wiring.argumentWire argument = right then
            some { node := 0, port := CPort.arg argument }
          else none)) = true
      have absent : endpoint ∉
          (allFin (signature.get definition)).filterMap (fun argument =>
            if wiring.argumentWire argument = right then
              some { node := 0, port := CPort.arg argument }
            else none) := by
        intro rightMember
        obtain ⟨rightArgument, _, rightMapped⟩ :=
          List.mem_filterMap.mp rightMember
        have rightWireEq : wiring.argumentWire rightArgument = right := by
          by_cases equal : wiring.argumentWire rightArgument = right
          · exact equal
          · have impossible : False := by simpa [equal] using rightMapped
            exact impossible.elim
        have rightEndpointEq :
            ({ node := 0, port := CPort.arg rightArgument } : CEndpoint 1) =
              endpoint := by
          have simplified := rightMapped
          rw [if_pos rightWireEq] at simplified
          exact Option.some.inj simplified
        apply bne_iff_ne.mp different
        rw [← leftWireEq, ← rightWireEq]
        apply congrArg wiring.argumentWire
        apply Fin.ext
        simpa using congrArg
          (fun endpoint : CEndpoint 1 => endpoint.port)
          (leftEndpointEq.trans rightEndpointEq.symm)
      rw [Bool.not_eq_true']
      exact decide_eq_false absent
    · intro node argument
      change Fin 1 at node
      have nodeEq : node = (0 : Fin 1) := Subsingleton.elim _ _
      subst node
      refine ⟨wiring.argumentWire argument, ?_⟩
      apply List.mem_filterMap.mpr
      refine ⟨argument, mem_allFin argument, ?_⟩
      have self : wiring.argumentWire argument =
          wiring.argumentWire argument := rfl
      rw [if_pos self]
      rfl
    · intro wire endpoint endpointMember
      exact ConcreteDiagram.Encloses.refl _ _
  · intro wire _
    rfl

def wiredNamedReferencePattern (signature : List Nat)
    (definition : Fin signature.length)
    (wiring : NamedReferenceWiring (signature.get definition)) :
    CheckedOpenDiagram signature :=
  ⟨wiredNamedReferencePatternRaw signature definition wiring,
    wiredNamedReferencePatternRaw_wellFormed signature definition wiring⟩

@[simp] theorem wiredNamedReferencePattern_boundary_length
    (signature : List Nat) (definition : Fin signature.length)
    (wiring : NamedReferenceWiring (signature.get definition)) :
    (wiredNamedReferencePatternRaw signature definition wiring).boundary.length =
      signature.get definition := by
  simp [wiredNamedReferencePatternRaw]

theorem namedReferencePattern_boundary_length
    (signature : List Nat) (definition : Fin signature.length) :
    (namedReferencePatternRaw signature definition).boundary.length =
      signature.get definition := by
  simp [namedReferencePatternRaw, allFin_eq_finRange]

end VisualProof.Rule
