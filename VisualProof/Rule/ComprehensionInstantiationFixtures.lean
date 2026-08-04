import VisualProof.Rule.Comprehension

namespace VisualProof.Rule.ComprehensionInstantiationFixtures

open VisualProof
open VisualProof.Diagram
open VisualProof.Diagram.Splice.AttachmentAliasMaterialization

/-- Two bound atoms observe different repeated-boundary attachment partitions:
the first sees `[left, right, right]`; the second sees
`[left, left, left]`.  Both retained wires are root-scoped so the final receipt
can exercise its ordered open-interface transport. -/
def multiAtomHostRaw : ConcreteDiagram where
  regionCount := 3
  nodeCount := 2
  wireCount := 2
  root := 0
  regions := fun region =>
    if region = 0 then .sheet
    else if region = 1 then .cut 0
    else .bubble 1 3
  nodes := fun _ => .atom 2 2
  wires := fun wire =>
    if wire = 0 then {
      scope := 0
      endpoints := [
        { node := 0, port := .arg 0 },
        { node := 1, port := .arg 0 },
        { node := 1, port := .arg 1 },
        { node := 1, port := .arg 2 }
      ]
    } else {
      scope := 0
      endpoints := [
        { node := 0, port := .arg 1 },
        { node := 0, port := .arg 2 }
      ]
    }

theorem multiAtomHostRaw_check :
    ∃ checked, checkWellFormed [] multiAtomHostRaw = .ok checked ∧
      checked.val = multiAtomHostRaw := by
  refine ⟨_, rfl, rfl⟩

def multiAtomHost : CheckedDiagram [] :=
  ⟨multiAtomHostRaw, checkWellFormed_iff.mp multiAtomHostRaw_check⟩

def selectedBubble : Fin multiAtomHost.val.regionCount := ⟨2, by decide⟩

def repeatedBoundaryRaw : OpenConcreteDiagram where
  diagram := {
    regionCount := 1
    nodeCount := 0
    wireCount := 1
    root := 0
    regions := fun _ => .sheet
    nodes := nofun
    wires := fun _ => { scope := 0, endpoints := [] }
  }
  boundary := [0, 0, 0]

theorem repeatedBoundaryDiagram_check :
    ∃ checked,
      checkWellFormed [] repeatedBoundaryRaw.diagram = .ok checked ∧
        checked.val = repeatedBoundaryRaw.diagram := by
  refine ⟨_, rfl, rfl⟩

def repeatedBoundary : CheckedOpenDiagram [] :=
  ⟨repeatedBoundaryRaw, {
    diagram_well_formed := checkWellFormed_iff.mp repeatedBoundaryDiagram_check
    boundary_is_root_scoped := by
      intro wire _
      simp [repeatedBoundaryRaw]
  }⟩

def payload : ComprehensionInstantiatePayload multiAtomHost selectedBubble
    repeatedBoundary [] [] where
  parent := ⟨1, by decide⟩
  arity := 3
  bubble_eq := by native_decide
  boundarySplit := rfl
  parameterScopesProper := nofun
  binderSpine := emptyBinderSpine repeatedBoundary
  terminalBody := emptyTerminalBody repeatedBoundary
  binderTargets := nofun
  binderPairsExact := rfl
  binderTargetsProper := nofun

def copyRunStatus : Bool :=
  match instantiateCopies repeatedBoundary [] [] payload 2
      (initialInstantiationState payload) with
  | .error _ => false
  | .ok result =>
      result.pendingAtoms.isEmpty && result.processedAtoms.length == 2

/-- The actual two-copy executor consumes both atoms successfully. -/
example : copyRunStatus = true := by native_decide

/-- Observe the same plan sequence selected by `instantiateCopies`, recording
the exact count of attachment-sensitive identities added for each atom. -/
def plannedAliasCounts? : Option (Nat × Nat) :=
  let initial := initialInstantiationState payload
  match initial.pendingAtoms with
  | [] => none
  | firstAtom :: firstTail =>
      match initial.diagram.val.nodes firstAtom with
      | .term .. | .named .. => none
      | .atom firstSite firstCandidate =>
          if firstCandidate = initial.bubble then
            match instantiateArguments? initial firstAtom payload.arity with
            | none => none
            | some firstArguments =>
                match planInstantiationCopy repeatedBoundary [] [] payload
                    initial firstAtom firstTail firstSite firstArguments with
                | .error _ => none
                | .ok firstPlan =>
                    let next := firstPlan.next
                    match next.pendingAtoms with
                    | [] => none
                    | secondAtom :: secondTail =>
                        match next.diagram.val.nodes secondAtom with
                        | .term .. | .named .. => none
                        | .atom secondSite secondCandidate =>
                            if secondCandidate = next.bubble then
                              match instantiateArguments? next secondAtom
                                  payload.arity with
                              | none => none
                              | some secondArguments =>
                                  match planInstantiationCopy repeatedBoundary
                                      [] [] payload next secondAtom secondTail
                                      secondSite secondArguments with
                                  | .error _ => none
                                  | .ok secondPlan =>
                                      some
                                        (aliasCount repeatedBoundary.val
                                            firstPlan.attachment,
                                          aliasCount repeatedBoundary.val
                                            secondPlan.attachment)
                            else none
          else none

/-- Per-copy planning observes genuinely different attachment partitions: the
first copy materializes one extra identity and the second materializes none. -/
example : plannedAliasCounts? = some (1, 0) := by native_decide

def receiptInterfaceStatus : Bool :=
  match applyComprehensionInstantiate .forward multiAtomHost selectedBubble
      repeatedBoundary [] [] payload with
  | .error _ => false
  | .ok receipt =>
      match receipt.interface.transportBoundary
          [⟨1, by decide⟩, ⟨0, by decide⟩, ⟨1, by decide⟩] with
      | some [first, second, third] => first == third && first != second
      | _ => false

/-- The final receipt preserves caller order and repetition while keeping the
two retained host-wire identities distinct. -/
example : receiptInterfaceStatus = true := by native_decide

end VisualProof.Rule.ComprehensionInstantiationFixtures
