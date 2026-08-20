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
  site := fun frame targetHead ports target =>
    target = .mk [added] (.cons
      (.atom (targetHead.appendLeft [added])
        (Vars.append
          ((ports.map fun wire => frame.targetKeep wire).map
            fun wire => wire.appendLeft [added])
          (.cons (Var.appendRight _ .here) .nil))) .nil)

def rootFrame (outer before after arguments : List Sig) (added : Sig) :=
  Transform.Frame.replace outer before after
    [.rel (arguments ++ [added])] arguments

def targetHead (outer before after arguments : List Sig) (added : Sig) :
    Var (outer ++ (before ++ .rel (arguments ++ [added]) :: after))
      (.rel (arguments ++ [added])) :=
  Transform.Frame.insertedHead outer before after
    (.rel (arguments ++ [added]))

/-- Exact structural arity shift with one fresh site-local argument wire. -/
inductive Shift : Region outer → Region outer → Prop
  | mk
      (arguments before after : List Sig) (added : Sig)
      {items : ItemSeq (outer ++ (before ++ .rel arguments :: after))}
      {result : Region
        (outer ++ (before ++ .rel (arguments ++ [added]) :: after))}
      (itemsResult : Transform.ItemsResult (operation arguments added)
        (rootFrame outer before after arguments added)
        (targetHead outer before after arguments added) items result) :
      Shift (.mk (before ++ .rel arguments :: after) items)
        (Region.adjoinAt
          (before ++ .rel (arguments ++ [added]) :: after) .nil result)

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
