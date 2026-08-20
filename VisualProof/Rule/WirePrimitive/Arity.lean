import VisualProof.Rule.Relation
import VisualProof.Rule.WirePrimitive.Transform

namespace VisualProof.Rule.WirePrimitive

open Theory
open Diagram

namespace Arity

def Vars.append : Vars context left → Vars context right →
    Vars context (left ++ right)
  | .nil, right => right
  | .cons head tail, right => .cons head (Vars.append tail right)

@[simp] theorem Vars.append_map
    (left : Vars source leftSignatures)
    (right : Vars source rightSignatures)
    (rename : WireRenaming source target) :
    (Vars.append left right).map (fun wire => rename wire) =
      Vars.append (left.map fun wire => rename wire)
        (right.map fun wire => rename wire) := by
  induction left with
  | nil => rfl
  | cons head tail induction =>
      exact congrArg (Vars.cons (rename head)) induction

def operation (arguments : List Sig) (added : Sig) :
    Transform.Operation arguments where
  Data := fun {_ _ targetWires} _ =>
    Var targetWires (.rel (arguments ++ [added]))
  appendData := fun _ targetHead locals => targetHead.appendLeft locals
  SiteData := fun _ _ _ => PUnit
  site := fun frame targetHead ports _ =>
    .mk [added] (.cons
      (.atom (targetHead.appendLeft [added])
        (Vars.append
          ((ports.map fun wire => frame.targetKeep wire).map
            fun wire => wire.appendLeft [added])
          (.cons (Var.appendRight _ .here) .nil)))
      (.cons
        (.identity added 1 (fun _ => Var.appendRight _ .here))
        .nil))
  pin := fun _ targetHead => Transform.unaryPin targetHead

def rootFrame (outer before after arguments : List Sig) (added : Sig) :=
  Transform.Frame.replace outer before after
    [.rel (arguments ++ [added])] arguments

def targetHead (outer before after arguments : List Sig) (added : Sig) :
    Var (outer ++ (before ++ .rel (arguments ++ [added]) :: after))
      (.rel (arguments ++ [added])) :=
  Transform.Frame.insertedHead outer before after
    (.rel (arguments ++ [added]))

structure Shift.Description (outer : List Sig) where
  arguments : List Sig
  before : List Sig
  after : List Sig
  added : Sig
  items : ItemSeq (outer ++ (before ++ .rel arguments :: after))
  itemsEdit : Transform.ItemsEdit (operation arguments added)
    (rootFrame outer before after arguments added)
    (targetHead outer before after arguments added) items

def Shift.Description.source (description : Shift.Description outer) :
    Region outer :=
  .mk (description.before ++ .rel description.arguments :: description.after)
    description.items

def Shift.Description.target (description : Shift.Description outer) :
    Region outer :=
  Region.adjoinAt
    (description.before ++
      .rel (description.arguments ++ [description.added]) :: description.after)
    .nil description.itemsEdit.run

/-- Exact structural arity shift with one fresh site-local argument wire. -/
inductive Shift : Region outer → Region outer → Prop
  | mk (description : Shift.Description outer) :
      Shift description.source description.target

inductive Local : LocalRule
  | shift (step : Shift before after) : Local before after

end Arity

def Arity : Rule :=
  Contextual fun before after => symmetric Arity.Local before after

theorem Arity.iso
    (sourceIso : OpenDiagramIso source source')
    (step : Arity source target)
    (targetIso : OpenDiagramIso target target') :
    Arity source' target' :=
  Contextual.iso sourceIso step targetIso

end VisualProof.Rule.WirePrimitive
