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
  SiteData := fun _ _ _ => PUnit
  site := fun frame targetHead ports _ =>
    Region.singleton (.atom targetHead
      (Vars.duplicateAt before
        (ports.map fun wire => frame.targetKeep wire)))
  pin := fun _ targetHead => Transform.unaryPin targetHead

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

structure Duplicates.Description (outer : List Sig) where
  before : List Sig
  after : List Sig
  localBefore : List Sig
  localAfter : List Sig
  signature : Sig
  items : ItemSeq (outer ++ (localBefore ++
    .rel (before ++ signature :: after) :: localAfter))
  itemsEdit : Transform.ItemsEdit (operation before after signature)
    (rootFrame outer localBefore localAfter before after signature)
    (targetHead outer localBefore localAfter before after signature) items

def Duplicates.Description.source
    (description : Duplicates.Description outer) : Region outer :=
  .mk (description.localBefore ++
    .rel (description.before ++ description.signature :: description.after) ::
      description.localAfter) description.items

def Duplicates.Description.target
    (description : Duplicates.Description outer) : Region outer :=
  Region.adjoinAt (description.localBefore ++
    .rel (description.before ++ description.signature ::
      description.signature :: description.after) :: description.localAfter)
    .nil description.itemsEdit.run

inductive Duplicates : Region outer → Region outer → Prop
  | mk (description : Duplicates.Description outer) :
      Duplicates description.source description.target

inductive Local : LocalRule
  | duplicate (step : Duplicates before after) : Local before after

end Duplicate

namespace Projection

def Vars.dropAt (before : List Sig) :
    Vars context (before ++ signature :: after) → Vars context (before ++ after)
  := match before with
  | [] => fun
    | .cons _ rest => rest
  | _ :: restBefore => fun
    | .cons head tail => .cons head (Vars.dropAt restBefore tail)

def Vars.insertAt (before : List Sig) (inserted : Var context signature) :
    Vars context (before ++ after) →
      Vars context (before ++ signature :: after)
  := match before with
  | [] => fun rest => .cons inserted rest
  | _ :: restBefore => fun
    | .cons head tail => .cons head (Vars.insertAt restBefore inserted tail)

@[simp] theorem Vars.insertAt_map (before : List Sig)
    (inserted : Var source signature)
    (variables : Vars source (before ++ after))
    (rename : WireRenaming source target) :
    (Vars.insertAt before inserted variables).map (fun wire => rename wire) =
      Vars.insertAt before (rename inserted)
        (variables.map fun wire => rename wire) := by
  induction before with
  | nil => rfl
  | cons head tail induction =>
      cases variables with
      | cons first rest =>
        exact congrArg (Vars.cons (rename first)) (induction rest)

def Values.dropAt (before : List Sig) :
    Values model (before ++ signature :: after) →
      Values model (before ++ after)
  := match before with
  | [] => fun values => values.2
  | _ :: restBefore => fun values =>
      (values.1, Values.dropAt restBefore values.2)

def Values.insertAt (before : List Sig) (inserted : denoteSig model signature) :
    Values model (before ++ after) →
      Values model (before ++ signature :: after)
  := match before with
  | [] => fun rest => (inserted, rest)
  | _ :: restBefore => fun rest =>
      (rest.1, Values.insertAt restBefore inserted rest.2)

theorem Values.drop_insert (before : List Sig)
    (inserted : denoteSig model signature)
    (values : Values model (before ++ after)) :
    Values.dropAt before (Values.insertAt before inserted values) = values := by
  induction before with
  | nil => rfl
  | cons head tail induction =>
      cases values with
      | mk first rest =>
        simp only [Values.insertAt, Values.dropAt]
        rw [induction rest]

theorem evaluate_drop (before : List Sig)
    (variables : Vars context (before ++ signature :: after))
    (env : Values model context) :
    evaluateVars (Vars.dropAt before variables) env =
      Values.dropAt before (evaluateVars variables env) := by
  induction before with
  | nil => cases variables; rfl
  | cons head tail induction =>
      cases variables with
      | cons first rest =>
        simp only [Vars.dropAt, evaluateVars, Values.dropAt]
        rw [induction rest]

theorem evaluate_insert (before : List Sig)
    (inserted : Var context signature)
    (variables : Vars context (before ++ after))
    (env : Values model context) :
    evaluateVars (Vars.insertAt before inserted variables) env =
      Values.insertAt before (env.lookup inserted)
        (evaluateVars variables env) := by
  induction before with
  | nil => rfl
  | cons head tail induction =>
      cases variables with
      | cons first rest =>
        simp only [Vars.insertAt, evaluateVars, Values.insertAt]
        rw [induction rest]

def operation (before after : List Sig) (signature : Sig) :
    Transform.Operation (before ++ signature :: after) where
  Data := fun {_ _ targetWires} _ =>
    Var targetWires (.rel (before ++ after))
  appendData := fun _ targetHead locals => targetHead.appendLeft locals
  SiteData := fun _ _ _ => PUnit
  site := fun frame targetHead ports _ =>
    Region.singleton (.atom targetHead
      (Vars.dropAt before
        (ports.map fun wire => frame.targetKeep wire)))
  pin := fun _ targetHead => Transform.unaryPin targetHead

def uniformOperation (before after : List Sig) (signature : Sig) :
    Transform.Operation (before ++ signature :: after) where
  Data := fun {common _ targetWires} _ =>
    Var targetWires (.rel (before ++ after)) × Option (Var common signature)
  appendData := fun _ data locals =>
    (data.1.appendLeft locals, data.2.map fun wire => wire.appendLeft locals)
  SiteData := fun {common _sourceWires _targetWires} _frame data ports =>
    Σ attachment : Var common signature,
      { retained : Vars common (before ++ after) //
        data.2 = some attachment ∧
          ports = Vars.insertAt before attachment retained }
  site := fun frame data _ siteData =>
    Region.singleton (.atom data.1
      (siteData.2.val.map fun wire => frame.targetKeep wire))
  pin := fun _ data => Transform.unaryPin data.1

def rootFrame (outer localBefore localAfter before after : List Sig)
    (signature : Sig) :=
  Transform.Frame.replace outer localBefore localAfter
    [.rel (before ++ after)] (before ++ signature :: after)

def targetHead (outer localBefore localAfter before after : List Sig) :
    Var (outer ++ (localBefore ++ .rel (before ++ after) :: localAfter))
      (.rel (before ++ after)) :=
  Transform.Frame.insertedHead outer localBefore localAfter _

structure Drops.Description (outer : List Sig) where
  before : List Sig
  after : List Sig
  localBefore : List Sig
  localAfter : List Sig
  signature : Sig
  items : ItemSeq (outer ++ (localBefore ++
    .rel (before ++ signature :: after) :: localAfter))
  itemsEdit : Transform.ItemsEdit (operation before after signature)
    (rootFrame outer localBefore localAfter before after signature)
    (targetHead outer localBefore localAfter before after) items

def Drops.Description.source (description : Drops.Description outer) :
    Region outer :=
  .mk (description.localBefore ++
    .rel (description.before ++ description.signature :: description.after) ::
      description.localAfter) description.items

def Drops.Description.target (description : Drops.Description outer) :
    Region outer :=
  Region.adjoinAt (description.localBefore ++
    .rel (description.before ++ description.after) :: description.localAfter)
    .nil description.itemsEdit.run

inductive Drops : Region outer → Region outer → Prop
  | mk (description : Drops.Description outer) :
      Drops description.source description.target

structure UniformDrops.Description (outer : List Sig) where
  before : List Sig
  after : List Sig
  localBefore : List Sig
  localAfter : List Sig
  signature : Sig
  attachment : Option
    (Var (outer ++ (localBefore ++ localAfter)) signature)
  items : ItemSeq (outer ++ (localBefore ++
    .rel (before ++ signature :: after) :: localAfter))
  itemsEdit : Transform.ItemsEdit (uniformOperation before after signature)
    (rootFrame outer localBefore localAfter before after signature)
    (targetHead outer localBefore localAfter before after, attachment) items

def UniformDrops.Description.source
    (description : UniformDrops.Description outer) : Region outer :=
  .mk (description.localBefore ++
    .rel (description.before ++ description.signature :: description.after) ::
      description.localAfter) description.items

def UniformDrops.Description.target
    (description : UniformDrops.Description outer) : Region outer :=
  Region.adjoinAt (description.localBefore ++
    .rel (description.before ++ description.after) :: description.localAfter)
    .nil description.itemsEdit.run

inductive UniformDrops : Region outer → Region outer → Prop
  | mk (description : UniformDrops.Description outer) :
      UniformDrops description.source description.target

inductive Local.Description (outer : List Sig) : Type
  | extend (description : Drops.Description outer)
  | uniformDrop (description : UniformDrops.Description outer)
  | uniformExtend (description : UniformDrops.Description outer)

def Local.Description.source : Local.Description outer → Region outer
  | .extend description => description.target
  | .uniformDrop description => description.source
  | .uniformExtend description => description.target

def Local.Description.target : Local.Description outer → Region outer
  | .extend description => description.source
  | .uniformDrop description => description.target
  | .uniformExtend description => description.source

inductive Local : LocalRule
  | mk (description : Local.Description outer) :
      Local description.source description.target

end Projection

end Argument

def ArgumentDuplicate : Rule :=
  Contextual fun before after => symmetric Argument.Duplicate.Local before after

theorem ArgumentDuplicate.iso
    (sourceIso : OpenDiagramIso source source')
    (step : ArgumentDuplicate source target)
    (targetIso : OpenDiagramIso target target') :
    ArgumentDuplicate source' target' :=
  Contextual.iso sourceIso step targetIso

def ArgumentProjection : Rule :=
  Contextual Argument.Projection.Local

theorem ArgumentProjection.iso
    (sourceIso : OpenDiagramIso source source')
    (step : ArgumentProjection source target)
    (targetIso : OpenDiagramIso target target') :
    ArgumentProjection source' target' :=
  Contextual.iso sourceIso step targetIso

end VisualProof.Rule.WirePrimitive
