import VisualProof.Diagram.Rename
import VisualProof.Model

namespace VisualProof.Diagram

open VisualProof
open Theory

mutual
  /-- Semantic values of higher-order wire signatures. -/
  def denoteSig (model : Model) : Sig → Type
    | .iota => model.Carrier
    | .rel arguments => Values model arguments → Prop

  /-- A typed semantic environment in recursive context order. -/
  def Values (model : Model) : List Sig → Type
    | [] => PUnit
    | signature :: rest =>
        denoteSig model signature × Values model rest
end

namespace Values

def lookup (values : Values model context) :
    Var context signature → denoteSig model signature
  | .here => values.1
  | .there wire => lookup values.2 wire

def ofLookup
    (value : ∀ {signature}, Var context signature → denoteSig model signature) :
    Values model context :=
  match context with
  | [] => PUnit.unit
  | _ :: _ =>
      (value .here, ofLookup fun wire => value (.there wire))

@[simp] theorem lookup_ofLookup
    (value : ∀ {signature}, Var context signature → denoteSig model signature)
    (wire : Var context signature) :
    (ofLookup value).lookup wire = value wire := by
  induction context with
  | nil => exact nomatch wire
  | cons head rest induction =>
      cases wire with
      | here => rfl
      | there tail =>
          exact induction (value := fun wire => value (.there wire)) tail

def rename (renameWires : WireRenaming source target)
    (targetValues : Values model target) : Values model source :=
  ofLookup fun wire => targetValues.lookup (renameWires wire)

@[simp] theorem lookup_rename
    (renameWires : WireRenaming source target)
    (targetValues : Values model target)
    (wire : Var source signature) :
    (rename renameWires targetValues).lookup wire =
      targetValues.lookup (renameWires wire) :=
  lookup_ofLookup _ _

def append (left : Values model leftContext)
    (right : Values model rightContext) :
    Values model (leftContext ++ rightContext) :=
  match leftContext, left with
  | [], _ => right
  | _ :: _, (head, tail) => (head, append tail right)

@[simp] theorem lookup_append_left
    (left : Values model leftContext)
    (right : Values model rightContext)
    (wire : Var leftContext signature) :
    (append left right).lookup (wire.appendLeft rightContext) =
      left.lookup wire := by
  induction leftContext with
  | nil => exact nomatch wire
  | cons head rest induction =>
      cases left with
      | mk first tailValues =>
          cases wire with
          | here => rfl
          | there tail => exact induction tailValues tail

@[simp] theorem lookup_append_right
    (left : Values model leftContext)
    (right : Values model rightContext)
    (wire : Var rightContext signature) :
    (append left right).lookup (Var.appendRight leftContext wire) =
      right.lookup wire := by
  induction leftContext with
  | nil => rfl
  | cons head tail induction =>
      cases left with
      | mk first rest => exact induction rest

theorem ext (left right : Values model context)
    (lookupEq : ∀ {signature} (wire : Var context signature),
      left.lookup wire = right.lookup wire) : left = right := by
  induction context with
  | nil => cases left; cases right; rfl
  | cons signature rest induction =>
      cases left with
      | mk leftHead leftTail =>
          cases right with
          | mk rightHead rightTail =>
              have headEq : leftHead = rightHead := lookupEq .here
              have tailEq : leftTail = rightTail := by
                apply induction
                intro signature wire
                exact lookupEq (.there wire)
              rw [headEq, tailEq]

end Values

theorem Vars.eq_of_get_eq
    (left right : Vars context signatures)
    (getEq : ∀ position, left.get position = right.get position) :
    left = right := by
  induction signatures with
  | nil => cases left; cases right; rfl
  | cons signature rest induction =>
      cases left with
      | cons leftHead leftTail =>
          cases right with
          | cons rightHead rightTail =>
              have headEq : leftHead = rightHead :=
                getEq ⟨0, by simp⟩
              have tailEq : leftTail = rightTail := by
                apply induction
                intro position
                exact getEq position.succ
              rw [headEq, tailEq]

@[simp] theorem Vars.get_map
    (variables : Vars source signatures)
    (renameWires : WireRenaming source target)
    (position : Fin signatures.length) :
    (variables.map (fun wire => renameWires wire)).get position =
      renameWires (variables.get position) := by
  induction variables with
  | nil => exact Fin.elim0 position
  | cons head tail induction =>
      exact Fin.cases rfl (fun index => induction index) position

def evaluateVars (variables : Vars context signatures)
    (values : Values model context) : Values model signatures :=
  match variables with
  | .nil => PUnit.unit
  | .cons head tail =>
      (values.lookup head, evaluateVars tail values)

theorem evaluateVars_eq_of_lookup
    (variables : Vars context signatures)
    (left right : Values model context)
    (lookupEq : ∀ {signature} (wire : Var context signature),
      left.lookup wire = right.lookup wire) :
    evaluateVars variables left = evaluateVars variables right := by
  induction variables with
  | nil => rfl
  | cons head tail induction =>
      simp only [evaluateVars]
      rw [lookupEq head, induction]

theorem evaluateVars_map_eq
    (variables : Vars source signatures)
    (renameWires : WireRenaming source target)
    (sourceValues : Values model source)
    (targetValues : Values model target)
    (lookupEq : ∀ {signature} (wire : Var source signature),
      sourceValues.lookup wire =
        targetValues.lookup (renameWires wire)) :
    evaluateVars (variables.map (fun wire => renameWires wire)) targetValues =
      evaluateVars variables sourceValues := by
  induction variables with
  | nil => rfl
  | cons head tail induction =>
      simp only [Vars.map, evaluateVars]
      rw [← lookupEq head, induction]

end VisualProof.Diagram
