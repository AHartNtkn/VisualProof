import VisualProof.Diagram.Concrete.Semantics

namespace VisualProof.Theory

open VisualProof.Diagram

end VisualProof.Theory

namespace VisualProof.Diagram.CheckedOpenDiagram

/--
A body verified against a definition prefix remains verified after later
definitions are appended.  Existing named-reference indices are embedded into
the left summand; no reference is retargeted.
-/
def weakenRight (checked : CheckedOpenDiagram signature) (suffix : List Nat) :
    CheckedOpenDiagram (signature ++ suffix) where
  val := checked.val
  property := {
    diagram_well_formed := {
      checked.property.diagram_well_formed with
      named_references_resolve := by
        intro node
        have prior :=
          checked.property.diagram_well_formed.named_references_resolve node
        cases hnode : checked.val.diagram.nodes node with
        | term => trivial
        | atom => trivial
        | named region definition arity =>
            simp only [hnode] at prior ⊢
            obtain ⟨hdefinition, hvalue⟩ :=
              List.getElem?_eq_some_iff.mp prior
            apply List.getElem?_eq_some_iff.mpr
            refine ⟨by simp; omega, ?_⟩
            simpa [List.getElem_append_left hdefinition] using hvalue
    }
    boundary_is_root_scoped := checked.property.boundary_is_root_scoped
  }

@[simp] theorem weakenRight_val
    (checked : CheckedOpenDiagram signature) (suffix : List Nat) :
    (checked.weakenRight suffix).val = checked.val := rfl

theorem weakenRight_elaborate_body
    (checked : CheckedOpenDiagram signature) (suffix : List Nat) :
    (checked.weakenRight suffix).elaborate.body =
      checked.elaborate.body.renameNamed
        (NamedRenaming.appendRight signature suffix) := by
  obtain ⟨sourceBody, sourceKernel, sourceElaborates⟩ :=
    CheckedOpenDiagram.elaborate_body_computation checked
  obtain ⟨targetBody, targetKernel, targetElaborates⟩ :=
    CheckedOpenDiagram.elaborate_body_computation (checked.weakenRight suffix)
  have kernel := ConcreteElaboration.compileRoot?_appendRight
    checked.property.diagram_well_formed suffix checked.val.exposedWires
      checked.val.hiddenWires
  rw [sourceKernel] at kernel
  simp only [Option.map_some] at kernel
  have bodies : targetBody = sourceBody.renameNamed
      (NamedRenaming.appendRight signature suffix) :=
    Option.some.inj (targetKernel.symm.trans kernel)
  rw [targetElaborates, sourceElaborates, bodies]
  rfl

theorem weakenRight_denote
    (checked : CheckedOpenDiagram signature) (suffix : List Nat)
    (model : Lambda.LambdaModel)
    (sourceNamed : NamedEnv model.Carrier signature)
    (targetNamed : NamedEnv model.Carrier (signature ++ suffix))
    (agrees : NamedEnv.Agrees (NamedRenaming.appendRight signature suffix)
      sourceNamed targetNamed)
    (args : Fin checked.val.boundary.length → model.Carrier) :
    (checked.weakenRight suffix).denote model targetNamed args ↔
      checked.denote model sourceNamed args := by
  change denoteOpen model targetNamed (checked.weakenRight suffix).elaborate args ↔
    denoteOpen model sourceNamed checked.elaborate args
  unfold denoteOpen
  constructor
  · rintro ⟨assignment, hargs, hbody⟩
    let sourceAssignment : BoundaryAssignment checked.elaborate model.Carrier := {
      args := assignment.args
      classes := assignment.classes
      agrees := assignment.agrees
    }
    refine ⟨sourceAssignment, hargs, ?_⟩
    rw [checked.weakenRight_elaborate_body suffix] at hbody
    exact (denoteRegion_renameNamed (relCtx := []) model
      (NamedRenaming.appendRight signature suffix) sourceNamed targetNamed
      agrees sourceAssignment.classes PUnit.unit checked.elaborate.body).mp hbody
  · rintro ⟨assignment, hargs, hbody⟩
    let targetAssignment : BoundaryAssignment
        (checked.weakenRight suffix).elaborate model.Carrier := {
      args := assignment.args
      classes := assignment.classes
      agrees := assignment.agrees
    }
    refine ⟨targetAssignment, hargs, ?_⟩
    rw [checked.weakenRight_elaborate_body suffix]
    exact (denoteRegion_renameNamed (relCtx := []) model
      (NamedRenaming.appendRight signature suffix) sourceNamed targetNamed
      agrees targetAssignment.classes PUnit.unit checked.elaborate.body).mpr hbody

end VisualProof.Diagram.CheckedOpenDiagram

namespace VisualProof.Theory

open VisualProof.Diagram

/-- One relation body checked against exactly the preceding definition prefix. -/
structure Definition (signature : List Nat) where
  body : CheckedOpenDiagram signature

namespace Definition

def arity (definition : Definition signature) : Nat :=
  definition.body.val.boundary.length

end Definition

/-- Ordered definitions; extension changes the signature available to later bodies. -/
inductive VerifiedDefinitions : List Nat → Type
  | empty : VerifiedDefinitions []
  | append (prior : VerifiedDefinitions signature)
      (definition : Definition signature) :
      VerifiedDefinitions (signature ++ [definition.arity])

/-- The final-signature view of one prefix-verified definition. -/
structure DefinitionEntry (signature : List Nat)
    (index : Fin signature.length) where
  body : CheckedOpenDiagram signature
  body_arity : body.val.boundary.length = signature.get index

namespace VerifiedDefinitions

/--
The lookup table derived uniquely from the ordered definition chain.  Earlier
bodies are weakened through later signature extensions; no independent table
or cyclic body can be supplied.
-/
def entry : (definitions : VerifiedDefinitions signature) →
    (index : Fin signature.length) → DefinitionEntry signature index
  | .empty, index => Fin.elim0 index
  | @append priorSignature prior definition, index => by
      by_cases hprior : index.val < priorSignature.length
      · let priorIndex : Fin priorSignature.length := ⟨index.val, hprior⟩
        let priorEntry := entry prior priorIndex
        exact {
          body := priorEntry.body.weakenRight [definition.arity]
          body_arity := by
            simpa [priorEntry, priorIndex, List.get_eq_getElem,
              List.getElem_append_left hprior] using priorEntry.body_arity
        }
      · have hlast : index.val = priorSignature.length := by
          have hin := index.isLt
          simp only [List.length_append, List.length_cons, List.length_nil] at hin
          omega
        exact {
          body := definition.body.weakenRight [definition.arity]
          body_arity := by
            simp [Definition.arity, hlast, List.get_eq_getElem]
        }

end VerifiedDefinitions

structure SomeVerifiedDefinitions where
  signature : List Nat
  value : VerifiedDefinitions signature

structure RawDefinition where
  body : OpenConcreteDiagram

inductive DefinitionError
  | malformedBody (error : WFError)
  | boundaryNotRootScoped
  deriving DecidableEq

private def checkOpenBody (signature : List Nat) (body : OpenConcreteDiagram) :
    Except DefinitionError (CheckedOpenDiagram signature) :=
  match hcheck : checkWellFormed signature body.diagram with
  | .error error => .error (.malformedBody error)
  | .ok checked =>
      if hboundary : ∀ wire, wire ∈ body.boundary →
          (body.diagram.wires wire).scope = body.diagram.root then
        .ok ⟨body, {
          diagram_well_formed := by
            have heq := checkWellFormed_preserves_input hcheck
            simpa only [heq] using checked.property
          boundary_is_root_scoped := hboundary
        }⟩
      else
        .error .boundaryNotRootScoped

private def verifyFrom (raw : List RawDefinition)
    (prior : VerifiedDefinitions signature) :
    Except DefinitionError SomeVerifiedDefinitions :=
  match raw with
  | [] => .ok ⟨signature, prior⟩
  | head :: tail =>
      match checkOpenBody signature head.body with
      | .error error => .error error
      | .ok body =>
          verifyFrom tail (.append prior ⟨body⟩)
termination_by raw.length

/-- The sole raw-to-ordered-definition verifier. -/
def verifyDefinitions (raw : List RawDefinition) :
    Except DefinitionError SomeVerifiedDefinitions :=
  verifyFrom raw .empty

def verificationError (raw : List RawDefinition) : Option DefinitionError :=
  match verifyDefinitions raw with
  | .error error => some error
  | .ok _ => none

theorem verificationError_eq_none_iff (raw : List RawDefinition) :
    verificationError raw = none ↔
      ∃ verified, verifyDefinitions raw = .ok verified := by
  unfold verificationError
  split
  · rename_i error herror
    constructor
    · intro h
      contradiction
    · rintro ⟨verified, hverified⟩
      rw [herror] at hverified
      contradiction
  · rename_i verified hverified
    exact ⟨fun _ => ⟨verified, hverified⟩, fun _ => rfl⟩

theorem verifyDefinitions_empty :
    verifyDefinitions [] = .ok ⟨[], .empty⟩ := by
  simp [verifyDefinitions, verifyFrom]

namespace DefinitionExamples

def emptyBody : OpenConcreteDiagram where
  diagram := {
    regionCount := 1
    nodeCount := 0
    wireCount := 0
    root := 0
    regions := fun _ => .sheet
    nodes := nofun
    wires := nofun
  }
  boundary := []

def previousZeroArityBody : OpenConcreteDiagram where
  diagram := {
    regionCount := 1
    nodeCount := 1
    wireCount := 0
    root := 0
    regions := fun _ => .sheet
    nodes := fun _ => .named 0 0 0
    wires := nofun
  }
  boundary := []

def emptyDefinition : RawDefinition := ⟨emptyBody⟩

def previousZeroArityDefinition : RawDefinition :=
  ⟨previousZeroArityBody⟩

theorem ordered_backward_reference_accepts :
    ∃ verified,
      verifyDefinitions [emptyDefinition, previousZeroArityDefinition] =
        .ok verified := by
  apply (verificationError_eq_none_iff _).mp
  native_decide

theorem unknown_reference_rejects :
    verificationError [previousZeroArityDefinition] =
      some (.malformedBody .namedReferenceDoesNotResolve) := by
  native_decide

/-- A self-reference is unknown at its own prefix and is therefore rejected. -/
theorem self_reference_rejects :
    verificationError [previousZeroArityDefinition] =
      some (.malformedBody .namedReferenceDoesNotResolve) :=
  unknown_reference_rejects

/-- A forward edge, including the first edge of any cycle, is rejected. -/
theorem forward_or_cyclic_reference_rejects :
    verificationError
        [previousZeroArityDefinition, emptyDefinition] =
      some (.malformedBody .namedReferenceDoesNotResolve) := by
  native_decide

end DefinitionExamples

end VisualProof.Theory
