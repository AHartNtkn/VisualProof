import VisualProof.Diagram.Semantics

namespace VisualProof

/-- A variable packaged with its intrinsic signature. -/
abbrev PackedVar (ctx : List Sig) : Type :=
  Sigma fun sig => Var ctx sig

namespace Vars

/-- Forget only the boundary signature list, retaining every typed occurrence. -/
def entries : {args : List Sig} → Vars ctx args → List (PackedVar ctx)
  | [], .nil => []
  | _ :: _, .cons head tail => ⟨_, head⟩ :: entries tail

/-- A class occurs somewhere in an ordered boundary tuple. -/
def Contains (variables : Vars ctx args) (fiber : Var ctx sig) : Prop :=
  (⟨sig, fiber⟩ : PackedVar ctx) ∈ variables.entries

/-- A class occurs at an exact ordered boundary position. -/
def At (variables : Vars ctx args) (index : Nat)
    (fiber : Var ctx sig) : Prop :=
  variables.entries[index]? = some (⟨sig, fiber⟩ : PackedVar ctx)

end Vars

/--
An intrinsic diagram with an ordered external boundary. Repeated boundary
variables are the only representation of boundary aliases.
-/
structure OpenDiagram (defs : List (List Sig)) (args : List Sig) where
  classes : List Sig
  boundary : Vars classes args
  boundary_surjective :
    ∀ sig (fiber : Var classes sig), boundary.Contains fiber
  body : Region defs classes

/-- Values supplied at an open diagram's ordered boundary. -/
abbrev BoundaryEnv (pre : PreModel) (args : List Sig) : Type :=
  PreModel.Args pre.Domain args

namespace OpenDiagram

/-- Two ordered boundary positions expose one and the same intrinsic class. -/
def boundaryAliases (diagram : OpenDiagram defs args)
    (left right : Nat) : Prop :=
  ∃ (sig : Sig) (fiber : Var diagram.classes sig),
    diagram.boundary.At left fiber ∧ diagram.boundary.At right fiber

end OpenDiagram

/--
An open diagram denotes when one class environment projects to exactly the
supplied ordered boundary values and makes the body true.
-/
def denoteOpen (pre : PreModel) (definitions : DefinitionEnv pre defs)
    (diagram : OpenDiagram defs args) (values : BoundaryEnv pre args) : Prop :=
  ∃ env : Env pre diagram.classes,
    Vars.denote env diagram.boundary = values ∧
      denoteRegion pre definitions env diagram.body

namespace OpenDiagram

/-- Repeated boundary variables force the two supplied individual values equal. -/
theorem reject_unequal_alias
    (diagram : OpenDiagram defs [.iota, .iota])
    (pre : PreModel) (definitions : DefinitionEnv pre defs)
    (alias : diagram.boundaryAliases 0 1)
    (x y : pre.Domain .iota) (different : x ≠ y) :
    ¬ denoteOpen pre definitions diagram (x, (y, PUnit.unit)) := by
  intro denotes
  rcases denotes with ⟨env, boundaryValues, _⟩
  rcases alias with ⟨sig, fiber, firstAt, secondAt⟩
  cases diagram with
  | mk classes boundary boundary_surjective body =>
      cases boundary with
      | cons first tail =>
          cases tail with
          | cons second tail =>
              cases tail
              simp only [Vars.At, Vars.entries,
                List.getElem?_cons_zero, List.getElem?_cons_succ,
                Option.some.injEq] at firstAt secondAt
              cases firstAt
              cases secondAt
              have firstValue :=
                congrArg Prod.fst boundaryValues
              have secondValue :=
                congrArg (fun values => values.2.1) boundaryValues
              exact different (firstValue.symm.trans secondValue)

end OpenDiagram

/-! Executable alias acceptance example. -/

example (diagram : OpenDiagram defs [.iota, .iota])
    (pre : PreModel) (definitions : DefinitionEnv pre defs)
    (alias : diagram.boundaryAliases 0 1)
    (x y : pre.Domain .iota) (different : x ≠ y) :
    ¬ denoteOpen pre definitions diagram (x, (y, PUnit.unit)) := by
  exact diagram.reject_unequal_alias pre definitions alias x y different

end VisualProof
