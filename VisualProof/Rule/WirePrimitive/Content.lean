import VisualProof.Rule.Relation
import VisualProof.Rule.WirePrimitive.Transform

namespace VisualProof.Rule.WirePrimitive

open Theory
open Diagram

namespace Content

namespace Cut

def operation (arguments : List Sig) : Transform.Operation arguments where
  Data := fun {_ _ targetWires} _ => Var targetWires (.rel arguments)
  appendData := fun _ targetHead locals => targetHead.appendLeft locals
  SiteData := fun _ _ _ => PUnit
  site := fun frame targetHead ports _ =>
    Region.singleton (.cut (Region.singleton
      (.atom targetHead
        (ports.map fun wire => frame.targetKeep wire))))
  pin := fun _ targetHead => Transform.unaryPin targetHead

def rootFrame (outer before after arguments : List Sig) :=
  Transform.Frame.replace outer before after [.rel arguments] arguments

def targetHead (outer before after arguments : List Sig) :
    Var (outer ++ (before ++ .rel arguments :: after)) (.rel arguments) :=
  Transform.Frame.insertedHead outer before after (.rel arguments)

/-- Complete source-side description of one cut-wrap edit. -/
structure Wrap.Description (outer : List Sig) where
  arguments : List Sig
  before : List Sig
  after : List Sig
  items : ItemSeq (outer ++ (before ++ .rel arguments :: after))
  itemsEdit : Transform.ItemsEdit (operation arguments)
    (rootFrame outer before after arguments)
    (targetHead outer before after arguments) items

def Wrap.Description.source (description : Wrap.Description outer) :
    Region outer :=
  .mk (description.before ++ .rel description.arguments :: description.after)
    description.items

def Wrap.Description.target (description : Wrap.Description outer) :
    Region outer :=
  Region.adjoinAt
    (description.before ++ .rel description.arguments :: description.after)
    .nil description.itemsEdit.run

/-- Exact structural cut-wrapping of every application of one local wire. -/
inductive Wrap : Region outer → Region outer → Prop
  | mk (description : Wrap.Description outer) :
      Wrap description.source description.target

inductive Local : LocalRule
  | wrap (step : Wrap before after) : Local before after

end Cut

namespace Parallel

abbrev Heads (targetWires arguments : List Sig) :=
  Var targetWires (.rel arguments) × Var targetWires (.rel arguments)

def operation (arguments : List Sig) : Transform.Operation arguments where
  Data := fun {_ _ targetWires} _ => Heads targetWires arguments
  appendData := fun _ heads locals =>
    (heads.1.appendLeft locals, heads.2.appendLeft locals)
  SiteData := fun _ _ _ => PUnit
  site := fun frame heads ports _ =>
    (Region.singleton (.atom heads.1
        (ports.map fun wire => frame.targetKeep wire))).conjoin
      (Region.singleton (.atom heads.2
        (ports.map fun wire => frame.targetKeep wire)))
  pin := fun _ heads =>
    (Transform.unaryPin heads.1).conjoin (Transform.unaryPin heads.2)

def rootFrame (outer before after arguments : List Sig) :=
  Transform.Frame.replace outer before after
    [.rel arguments, .rel arguments] arguments

def firstHead (outer before after arguments : List Sig) :
    Var (outer ++ (before ++ .rel arguments :: .rel arguments :: after))
      (.rel arguments) :=
  Transform.Frame.insertedHead outer before
    (.rel arguments :: after) (.rel arguments)

def secondHead (outer before after arguments : List Sig) :
    Var (outer ++ (before ++ .rel arguments :: .rel arguments :: after))
      (.rel arguments) :=
  Var.appendRight outer (Var.appendRight before (.there .here))

structure Split.Description (outer : List Sig) where
  arguments : List Sig
  before : List Sig
  after : List Sig
  items : ItemSeq (outer ++ (before ++ .rel arguments :: after))
  itemsEdit : Transform.ItemsEdit (operation arguments)
    (rootFrame outer before after arguments)
    (firstHead outer before after arguments,
      secondHead outer before after arguments) items

def Split.Description.source (description : Split.Description outer) :
    Region outer :=
  .mk (description.before ++ .rel description.arguments :: description.after)
    description.items

def Split.Description.target (description : Split.Description outer) :
    Region outer :=
  Region.adjoinAt
    (description.before ++ .rel description.arguments ::
      .rel description.arguments :: description.after)
    .nil description.itemsEdit.run

/-- Exact structural parallel splitting of every application of one local
wire into two co-located applications. -/
inductive Split : Region outer → Region outer → Prop
  | mk (description : Split.Description outer) :
      Split description.source description.target

inductive Local : LocalRule
  | split (step : Split before after) : Local before after

end Parallel

namespace Ends

def operation (arguments : List Sig) : Transform.Operation arguments where
  Data := fun _ => PUnit
  appendData := fun _ _ _ => PUnit.unit
  SiteData := fun _ _ _ => PUnit
  site := fun _ _ _ _ => Region.blank _
  pin := fun _ _ => Region.blank _

def rootFrame (outer before after arguments : List Sig) :=
  Transform.Frame.replace outer before after [] arguments

structure Delete.Description (outer : List Sig) where
  arguments : List Sig
  before : List Sig
  after : List Sig
  items : ItemSeq (outer ++ (before ++ .rel arguments :: after))
  itemsEdit : Transform.ItemsEdit (operation arguments)
    (rootFrame outer before after arguments) PUnit.unit items

def Delete.Description.source (description : Delete.Description outer) :
    Region outer :=
  .mk (description.before ++ .rel description.arguments :: description.after)
    description.items

def Delete.Description.target (description : Delete.Description outer) :
    Region outer :=
  Region.adjoinAt (description.before ++ description.after) .nil
    description.itemsEdit.run

/-- Exact structural replacement of every application of one local wire by
truth. Spawn uses every such edit; positive absorption additionally requires
the cut-parity guard below. -/
inductive Delete : Region outer → Region outer → Prop
  | mk (description : Delete.Description outer) :
      Delete description.source description.target

namespace Absorb

def flip : Polarity → Polarity
  | .positive => .negative
  | .negative => .positive

mutual
  /-- Evidence that every selected application in a region edit occurs
  positively. -/
  inductive RegionGuard :
      (polarity : Polarity) →
      {common sourceWires targetWires : List Sig} →
      (frame : Transform.Frame arguments common sourceWires targetWires) →
      {source : Region sourceWires} →
      Transform.RegionEdit (operation arguments) frame PUnit.unit source → Type
    | mk
        (itemsGuard : ItemsGuard polarity
          (Transform.Frame.append frame locals) itemsEdit) :
        RegionGuard polarity frame (.mk itemsEdit)

  /-- Evidence that every selected application in an item sequence occurs
  positively. -/
  inductive ItemsGuard :
      (polarity : Polarity) →
      {common sourceWires targetWires : List Sig} →
      (frame : Transform.Frame arguments common sourceWires targetWires) →
      {items : ItemSeq sourceWires} →
      Transform.ItemsEdit (operation arguments) frame PUnit.unit items → Type
    | nil : ItemsGuard polarity frame .nil
    | cons
        (itemGuard : ItemGuard polarity frame itemEdit)
        (tailGuard : ItemsGuard polarity frame tailEdit) :
        ItemsGuard polarity frame (.cons itemEdit tailEdit)

  /-- Selected atoms are admitted only at even cut depth. Unary pins denote
  truth and therefore remain admissible at either parity. -/
  inductive ItemGuard :
      (polarity : Polarity) →
      {common sourceWires targetWires : List Sig} →
      (frame : Transform.Frame arguments common sourceWires targetWires) →
      {item : Item sourceWires} →
      Transform.ItemEdit (operation arguments) frame PUnit.unit item → Type
    | atom
        (head : Var common (.rel atomArguments))
        (ports : Vars common atomArguments) :
        ItemGuard polarity frame (.atom head ports)
    | selectedAtom (ports : Vars common arguments) :
        ItemGuard .positive frame (.selectedAtom ports PUnit.unit)
    | selectedPin
        (ports : Fin 1 → Var sourceWires (.rel arguments))
        (selected : ports 0 = frame.selected) :
        ItemGuard polarity frame (.selectedPin ports selected)
    | identity
        (signature : Sig) (arity : Nat)
        (ports : Fin arity → Var common signature) :
        ItemGuard polarity frame (.identity signature arity ports)
    | term
        (output : Var common .iota) (freeArity : Nat)
        (ports : Fin freeArity → Var common .iota)
        (term : Lambda.Term 0 (Fin freeArity)) :
        ItemGuard polarity frame (.term output freeArity ports term)
    | cut
        (bodyEdit : Transform.RegionEdit (operation arguments)
          frame PUnit.unit body)
        (bodyGuard : RegionGuard (flip polarity) frame bodyEdit) :
        ItemGuard polarity frame (.cut bodyEdit)
end

mutual
  def RegionGuard.build
      (polarity : Polarity)
      {common sourceWires targetWires : List Sig}
      {frame : Transform.Frame arguments common sourceWires targetWires}
      {source : Region sourceWires}
      (edit : Transform.RegionEdit (operation arguments) frame PUnit.unit source) :
      Option (RegionGuard polarity frame edit) :=
    match edit with
    | .mk itemsEdit =>
        match ItemsGuard.build polarity itemsEdit with
        | some guard => some (.mk guard)
        | none => none

  def ItemsGuard.build
      (polarity : Polarity)
      {common sourceWires targetWires : List Sig}
      {frame : Transform.Frame arguments common sourceWires targetWires}
      {items : ItemSeq sourceWires}
      (edit : Transform.ItemsEdit (operation arguments) frame PUnit.unit items) :
      Option (ItemsGuard polarity frame edit) :=
    match edit with
    | .nil => some .nil
    | .cons itemEdit tailEdit =>
        match ItemGuard.build polarity itemEdit,
            ItemsGuard.build polarity tailEdit with
        | some itemGuard, some tailGuard => some (.cons itemGuard tailGuard)
        | _, _ => none

  def ItemGuard.build
      (polarity : Polarity)
      {common sourceWires targetWires : List Sig}
      {frame : Transform.Frame arguments common sourceWires targetWires}
      {item : Item sourceWires}
      (edit : Transform.ItemEdit (operation arguments) frame PUnit.unit item) :
      Option (ItemGuard polarity frame edit) :=
    match edit with
    | .atom head ports => some (.atom head ports)
    | .selectedAtom ports _ =>
        match polarity with
        | .positive => some (.selectedAtom ports)
        | .negative => none
    | .selectedPin ports selected => some (.selectedPin ports selected)
    | .identity signature arity ports => some (.identity signature arity ports)
    | .term output freeArity ports term =>
        some (.term output freeArity ports term)
    | .cut bodyEdit =>
        match RegionGuard.build (flip polarity) bodyEdit with
        | some bodyGuard => some (.cut bodyEdit bodyGuard)
        | none => none
end

structure Description (outer : List Sig) where
  deletion : Delete.Description outer
  guard : ItemsGuard .positive
    (rootFrame outer deletion.before deletion.after deletion.arguments)
    deletion.itemsEdit

def Description.build (deletion : Delete.Description outer) :
    Option { description : Description outer //
      description.deletion = deletion } :=
  match ItemsGuard.build .positive deletion.itemsEdit with
  | some guard => some ⟨⟨deletion, guard⟩, rfl⟩
  | none => none

def Description.source (description : Description outer) : Region outer :=
  description.deletion.source

def Description.target (description : Description outer) : Region outer :=
  description.deletion.target

end Absorb

inductive Absorb : Region outer → Region outer → Prop
  | mk (description : Absorb.Description outer) :
      Absorb description.source description.target

inductive Local : LocalRule
  | spawn (step : Delete applied empty) : Local empty applied
  | absorb (step : Absorb applied empty) : Local applied empty

end Ends

end Content

def CutShape : Rule :=
  Contextual fun before after => symmetric Content.Cut.Local before after

def ParallelShape : Rule :=
  Contextual fun before after => symmetric Content.Parallel.Local before after

def Ends : Rule :=
  Contextual fun before after => Content.Ends.Local before after

theorem CutShape.iso
    (sourceIso : OpenDiagramIso source source')
    (step : CutShape source target)
    (targetIso : OpenDiagramIso target target') :
    CutShape source' target' :=
  Contextual.iso sourceIso step targetIso

theorem ParallelShape.iso
    (sourceIso : OpenDiagramIso source source')
    (step : ParallelShape source target)
    (targetIso : OpenDiagramIso target target') :
    ParallelShape source' target' :=
  Contextual.iso sourceIso step targetIso

theorem Ends.iso
    (sourceIso : OpenDiagramIso source source')
    (step : Ends source target)
    (targetIso : OpenDiagramIso target target') :
    Ends source' target' :=
  Contextual.iso sourceIso step targetIso

end VisualProof.Rule.WirePrimitive
