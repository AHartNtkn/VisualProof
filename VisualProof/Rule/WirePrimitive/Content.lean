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
  site := fun frame targetHead ports target =>
    target = Region.singleton (.cut (Region.singleton
      (.atom targetHead
        (ports.map fun wire => frame.targetKeep wire))))

def rootFrame (outer before after arguments : List Sig) :=
  Transform.Frame.replace outer before after [.rel arguments] arguments

def targetHead (outer before after arguments : List Sig) :
    Var (outer ++ (before ++ .rel arguments :: after)) (.rel arguments) :=
  Transform.Frame.insertedHead outer before after (.rel arguments)

/-- Exact structural cut-wrapping of every application of one local wire. -/
inductive Wrap : Region outer → Region outer → Prop
  | mk
      (arguments before after : List Sig)
      {items : ItemSeq (outer ++ (before ++ .rel arguments :: after))}
      {result : Region (outer ++ (before ++ .rel arguments :: after))}
      (itemsResult : Transform.ItemsResult (operation arguments)
        (rootFrame outer before after arguments)
        (targetHead outer before after arguments) items result) :
      Wrap (.mk (before ++ .rel arguments :: after) items)
        (Region.adjoinAt (before ++ .rel arguments :: after) .nil result)

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
  site := fun frame heads ports target =>
    target =
      (Region.singleton (.atom heads.1
        (ports.map fun wire => frame.targetKeep wire))).conjoin
      (Region.singleton (.atom heads.2
        (ports.map fun wire => frame.targetKeep wire)))

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

/-- Exact structural parallel splitting of every application of one local
wire into two co-located applications. -/
inductive Split : Region outer → Region outer → Prop
  | mk
      (arguments before after : List Sig)
      {items : ItemSeq (outer ++ (before ++ .rel arguments :: after))}
      {result : Region
        (outer ++ (before ++ .rel arguments :: .rel arguments :: after))}
      (itemsResult : Transform.ItemsResult (operation arguments)
        (rootFrame outer before after arguments)
        (firstHead outer before after arguments,
          secondHead outer before after arguments) items result) :
      Split (.mk (before ++ .rel arguments :: after) items)
        (Region.adjoinAt
          (before ++ .rel arguments :: .rel arguments :: after) .nil result)

inductive Local : LocalRule
  | split (step : Split before after) : Local before after

end Parallel

namespace Ends

def operation (arguments : List Sig) : Transform.Operation arguments where
  Data := fun _ => PUnit
  appendData := fun _ _ _ => PUnit.unit
  site := fun _ _ _ target => target = Region.blank _

def rootFrame (outer before after arguments : List Sig) :=
  Transform.Frame.replace outer before after [] arguments

/-- Exact structural deletion of every application of one local wire. The
local rule is oriented in the sound spawn direction; contextual polarity
supplies deletion in negative position. -/
inductive Delete : Region outer → Region outer → Prop
  | mk
      (arguments before after : List Sig)
      {items : ItemSeq (outer ++ (before ++ .rel arguments :: after))}
      {result : Region (outer ++ (before ++ after))}
      (itemsResult : Transform.ItemsResult (operation arguments)
        (rootFrame outer before after arguments) PUnit.unit items result) :
      Delete (.mk (before ++ .rel arguments :: after) items)
        (Region.adjoinAt (before ++ after) .nil result)

inductive Local : LocalRule
  | spawn (step : Delete applied empty) : Local empty applied

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
