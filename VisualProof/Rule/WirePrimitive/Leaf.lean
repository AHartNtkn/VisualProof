import VisualProof.Rule.Relation
import VisualProof.Rule.WirePrimitive.Argument

namespace VisualProof.Rule.WirePrimitive

open Theory
open Diagram

namespace Leaf

namespace Formal

def operation (before after : List Sig) :
    Transform.Operation (before ++ .rel (before ++ after) :: after) where
  Data := fun _ => PUnit
  appendData := fun _ _ _ => PUnit.unit
  site := fun frame _ ports target =>
    ∃ (formal : Var _ (.rel (before ++ after)))
      (retained : Vars _ (before ++ after)),
      ports = Argument.Projection.Vars.insertAt before formal retained ∧
      target = Region.singleton
        (.atom (frame.targetKeep formal)
          (retained.map fun wire => frame.targetKeep wire))

def rootFrame (outer localBefore localAfter before after : List Sig) :=
  Transform.Frame.replace outer localBefore localAfter []
    (before ++ .rel (before ++ after) :: after)

inductive Applies : Region outer → Region outer → Prop
  | mk
      (before after localBefore localAfter : List Sig)
      {items : ItemSeq (outer ++ (localBefore ++
        .rel (before ++ .rel (before ++ after) :: after) :: localAfter))}
      {result : Region (outer ++ (localBefore ++ localAfter))}
      (itemsResult : Transform.ItemsResult (operation before after)
        (rootFrame outer localBefore localAfter before after) PUnit.unit
        items result) :
      Applies
        (.mk (localBefore ++
          .rel (before ++ .rel (before ++ after) :: after) :: localAfter) items)
        (Region.adjoinAt (localBefore ++ localAfter) .nil result)

inductive Local : LocalRule
  | abstractFormal (step : Applies applied formal) : Local formal applied

end Formal

namespace Identity

def wire (signature : Sig) : {arity : Nat} →
    Fin arity → Var (List.replicate arity signature) signature
  | 0, position => Fin.elim0 position
  | _ + 1, position =>
      Fin.cases .here (fun rest => .there (wire signature rest)) position

def Vars.fromFn (ports : Fin arity → Var context signature) :
    Vars context (List.replicate arity signature) :=
  match arity with
  | 0 => .nil
  | _ + 1 => .cons (ports 0)
      (Vars.fromFn fun position => ports position.succ)

@[simp] theorem Vars.fromFn_map
    (ports : Fin arity → Var source signature)
    (rename : WireRenaming source target) :
    (Vars.fromFn ports).map (fun wire => rename wire) =
      Vars.fromFn (fun position => rename (ports position)) := by
  induction arity with
  | zero => rfl
  | succ arity induction =>
      simp only [Vars.fromFn, Vars.map]
      exact congrArg (Vars.cons (rename (ports 0)))
        (induction (ports := fun position => ports position.succ))

theorem Values.lookup_evaluate_fromFn
    (ports : Fin arity → Var context signature)
    (env : Values model context) (position : Fin arity) :
    (evaluateVars (Vars.fromFn ports) env).lookup (wire signature position) =
      env.lookup (ports position) := by
  induction arity with
  | zero => exact Fin.elim0 position
  | succ arity induction =>
      refine Fin.cases rfl (fun rest => ?_) position
      exact induction (ports := fun index => ports index.succ) rest

def operation (signature : Sig) (arity : Nat) :
    Transform.Operation (List.replicate arity signature) where
  Data := fun _ => PUnit
  appendData := fun _ _ _ => PUnit.unit
  site := fun frame _ ports target =>
    ∃ identityPorts : Fin arity → Var _ signature,
      ports = Vars.fromFn identityPorts ∧
      target = Region.singleton (.identity signature arity
        (fun position => frame.targetKeep (identityPorts position)))

def rootFrame (outer localBefore localAfter : List Sig)
    (signature : Sig) (arity : Nat) :=
  Transform.Frame.replace outer localBefore localAfter []
    (List.replicate arity signature)

inductive Leaves : Region outer → Region outer → Prop
  | mk
      (signature : Sig) (arity : Nat) (arityAtLeastTwo : 2 ≤ arity)
      (localBefore localAfter : List Sig)
      {items : ItemSeq (outer ++ (localBefore ++
        .rel (List.replicate arity signature) :: localAfter))}
      {result : Region (outer ++ (localBefore ++ localAfter))}
      (itemsResult : Transform.ItemsResult (operation signature arity)
        (rootFrame outer localBefore localAfter signature arity) PUnit.unit
        items result) :
      Leaves
        (.mk (localBefore ++
          .rel (List.replicate arity signature) :: localAfter) items)
        (Region.adjoinAt (localBefore ++ localAfter) .nil result)

inductive Local : LocalRule
  | abstractIdentity (step : Leaves applied identity) : Local identity applied

end Identity

end Leaf

def FormalApplication : Rule :=
  Contextual Leaf.Formal.Local

theorem FormalApplication.iso
    (sourceIso : OpenDiagramIso source source')
    (step : FormalApplication source target)
    (targetIso : OpenDiagramIso target target') :
    FormalApplication source' target' :=
  Contextual.iso sourceIso step targetIso

def IdentityLeaf : Rule :=
  Contextual Leaf.Identity.Local

theorem IdentityLeaf.iso
    (sourceIso : OpenDiagramIso source source')
    (step : IdentityLeaf source target)
    (targetIso : OpenDiagramIso target target') :
    IdentityLeaf source' target' :=
  Contextual.iso sourceIso step targetIso

end VisualProof.Rule.WirePrimitive
