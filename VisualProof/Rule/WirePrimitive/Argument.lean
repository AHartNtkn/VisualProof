import VisualProof.Rule.Relation
import VisualProof.Rule.WirePrimitive.Transform

namespace VisualProof.Rule.WirePrimitive

open Theory
open Diagram

namespace Argument

namespace Duplicate

def Vars.duplicateAt (before : List Sig) :
    Vars context (before ++ signature :: after) →
      Vars context (before ++ signature :: signature :: after)
  := match before with
  | [] => fun
    | .cons selected rest => .cons selected (.cons selected rest)
  | _ :: restBefore => fun
    | .cons head tail => .cons head (Vars.duplicateAt restBefore tail)

def Values.duplicateAt (before : List Sig) :
    Values model (before ++ signature :: after) →
      Values model (before ++ signature :: signature :: after)
  := match before with
  | [] => fun values => (values.1, values.1, values.2)
  | _ :: restBefore => fun values =>
      (values.1, Values.duplicateAt restBefore values.2)

def Values.contractAt (before : List Sig) :
    Values model (before ++ signature :: signature :: after) →
      Values model (before ++ signature :: after)
  := match before with
  | [] => fun values => (values.1, values.2.2)
  | _ :: restBefore => fun values =>
      (values.1, Values.contractAt restBefore values.2)

theorem Values.contract_duplicate (before : List Sig)
    (values : Values model (before ++ signature :: after)) :
    Values.contractAt before (Values.duplicateAt before values) = values := by
  induction before with
  | nil => cases values; rfl
  | cons head tail induction =>
      cases values with
      | mk first rest =>
        simp only [Values.duplicateAt, Values.contractAt]
        rw [induction rest]

theorem evaluate_duplicate (before : List Sig)
    (variables : Vars context (before ++ signature :: after))
    (env : Values model context) :
    evaluateVars (Vars.duplicateAt before variables) env =
      Values.duplicateAt before (evaluateVars variables env) := by
  induction before with
  | nil => cases variables; rfl
  | cons head tail induction =>
      cases variables with
      | cons first rest =>
        simp only [Vars.duplicateAt, evaluateVars, Values.duplicateAt]
        rw [induction rest]

def operation (before after : List Sig) (signature : Sig) :
    Transform.Operation (before ++ signature :: after) where
  Data := fun {_ _ targetWires} _ =>
    Var targetWires (.rel (before ++ signature :: signature :: after))
  appendData := fun _ targetHead locals => targetHead.appendLeft locals
  site := fun frame targetHead ports target =>
    target = Region.singleton (.atom targetHead
      (Vars.duplicateAt before
        (ports.map fun wire => frame.targetKeep wire)))

def rootFrame (outer localBefore localAfter before after : List Sig)
    (signature : Sig) :=
  Transform.Frame.replace outer localBefore localAfter
    [.rel (before ++ signature :: signature :: after)]
    (before ++ signature :: after)

def targetHead (outer localBefore localAfter before after : List Sig)
    (signature : Sig) :
    Var (outer ++ (localBefore ++
      .rel (before ++ signature :: signature :: after) :: localAfter))
      (.rel (before ++ signature :: signature :: after)) :=
  Transform.Frame.insertedHead outer localBefore localAfter _

inductive Duplicates : Region outer → Region outer → Prop
  | mk
      (before after localBefore localAfter : List Sig) (signature : Sig)
      {items : ItemSeq (outer ++ (localBefore ++
        .rel (before ++ signature :: after) :: localAfter))}
      {result : Region (outer ++ (localBefore ++
        .rel (before ++ signature :: signature :: after) :: localAfter))}
      (itemsResult : Transform.ItemsResult
        (operation before after signature)
        (rootFrame outer localBefore localAfter before after signature)
        (targetHead outer localBefore localAfter before after signature)
        items result) :
      Duplicates
        (.mk (localBefore ++ .rel (before ++ signature :: after) :: localAfter)
          items)
        (Region.adjoinAt (localBefore ++
          .rel (before ++ signature :: signature :: after) :: localAfter)
          .nil result)

inductive Local : LocalRule
  | duplicate (step : Duplicates before after) : Local before after

end Duplicate

end Argument

def ArgumentDuplicate : Rule :=
  Contextual fun before after => symmetric Argument.Duplicate.Local before after

theorem ArgumentDuplicate.iso
    (sourceIso : OpenDiagramIso source source')
    (step : ArgumentDuplicate source target)
    (targetIso : OpenDiagramIso target target') :
    ArgumentDuplicate source' target' :=
  Contextual.iso sourceIso step targetIso

end VisualProof.Rule.WirePrimitive
