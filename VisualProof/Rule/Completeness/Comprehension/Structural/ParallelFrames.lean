import VisualProof.Rule.Completeness.Comprehension.Structural.Parallel
import VisualProof.Rule.Completeness.Comprehension.Structural.Support

namespace VisualProof.Rule.Completeness.Comprehension

open Diagram
open Theory
open WirePrimitive

namespace Structural

theorem supportParallelAppendRightNil
    (wire : Var wires signature) : Var.appendRight [] wire = wire := by
  induction wire with
  | here => rfl
  | there wire induction => exact congrArg Var.there induction

/-- The one coherent pair of sequential comprehension frames underlying a
Parallel edit. The first child removes the first split binder, the second
removes the remaining binder, and their retained maps compose to the edit's
target map. -/
structure SupportParallelFrames
    {arguments common sourceWires splitWires middleWires : List Sig}
    (frame : Transform.Frame arguments common sourceWires splitWires)
    (data : (Content.Parallel.operation arguments).Data frame) where
  head : Transform.Frame arguments middleWires splitWires middleWires
  tail : Transform.Frame arguments common middleWires common
  headTarget : ∀ {signature} (wire : Var middleWires signature),
    head.targetKeep wire = wire
  tailTarget : ∀ {signature} (wire : Var common signature),
    tail.targetKeep wire = wire
  retained : ∀ {signature} (wire : Var common signature),
    head.sourceKeep (tail.sourceKeep wire) = frame.targetKeep wire
  first : head.selected = data.1
  second : head.sourceKeep tail.selected = data.2

def SupportParallelFrames.append
    {arguments common sourceWires splitWires middleWires locals : List Sig}
    {frame : Transform.Frame arguments common sourceWires splitWires}
    {data : (Content.Parallel.operation arguments).Data frame}
    (frames : SupportParallelFrames
      (middleWires := middleWires) frame data) :
    SupportParallelFrames (middleWires := middleWires ++ locals)
      (frame.append locals)
      ((Content.Parallel.operation arguments).appendData frame data locals) :=
  {
    head := frames.head.append locals
    tail := frames.tail.append locals
    headTarget := by
      intro signature wire
      apply Var.appendCases (left := middleWires) (right := locals)
        (motive := fun wire =>
          (frames.head.append locals).targetKeep wire = wire)
      · intro inheritedSignature inherited
        simpa [Transform.Frame.append, WireRenaming.appendRight] using
          congrArg (fun wire => wire.appendLeft locals)
            (frames.headTarget inherited)
      · intro localSignature localWire
        simp [Transform.Frame.append, WireRenaming.appendRight]
    tailTarget := by
      intro signature wire
      apply Var.appendCases (left := common) (right := locals)
        (motive := fun wire =>
          (frames.tail.append locals).targetKeep wire = wire)
      · intro inheritedSignature inherited
        simpa [Transform.Frame.append, WireRenaming.appendRight] using
          congrArg (fun wire => wire.appendLeft locals)
            (frames.tailTarget inherited)
      · intro localSignature localWire
        simp [Transform.Frame.append, WireRenaming.appendRight]
    retained := by
      intro signature wire
      apply Var.appendCases (left := common) (right := locals)
        (motive := fun wire =>
          ((frames.head.append locals).sourceKeep
              ((frames.tail.append locals).sourceKeep wire)) =
            (frame.append locals).targetKeep wire)
      · intro inheritedSignature inherited
        simpa [Transform.Frame.append, WireRenaming.appendRight] using
          congrArg (fun wire => wire.appendLeft locals)
            (frames.retained inherited)
      · intro localSignature localWire
        simp [Transform.Frame.append, WireRenaming.appendRight]
    first := by
      simpa [Content.Parallel.operation, Transform.Frame.append,
        WireRenaming.appendRight] using congrArg (fun wire =>
          wire.appendLeft locals) frames.first
    second := by
      simpa [Content.Parallel.operation, Transform.Frame.append,
        WireRenaming.appendRight] using congrArg (fun wire =>
          wire.appendLeft locals) frames.second
  }

def supportParallelRootFrames
    (outer before after arguments : List Sig) :
    SupportParallelFrames
      (middleWires :=
        outer ++ (before ++ .rel arguments :: after))
      (Content.Parallel.rootFrame outer before after arguments)
      (Content.Parallel.firstHead outer before after arguments,
        Content.Parallel.secondHead outer before after arguments) :=
  {
    head := Transform.Frame.replace outer before
      (.rel arguments :: after) [] arguments
    tail := Transform.Frame.replace outer before after [] arguments
    headTarget := by
      intro signature wire
      apply Var.appendCases (left := outer)
        (right := before ++ .rel arguments :: after)
        (motive := fun wire =>
          (Transform.Frame.replace outer before
            (.rel arguments :: after) [] arguments).targetKeep wire = wire)
      · intro inheritedSignature inherited
        simp [Transform.Frame.replace, Transform.Frame.keep]
      · intro localSignature localWire
        apply Var.appendCases (left := before)
          (right := .rel arguments :: after)
          (motive := fun localWire' =>
            (Transform.Frame.replace outer before
              (.rel arguments :: after) [] arguments).targetKeep
                (Var.appendRight outer localWire') =
                  Var.appendRight outer localWire')
        · intro beforeSignature beforeWire
          simp [Transform.Frame.replace, Transform.Frame.keep,
            Transform.Frame.localKeep]
        · intro afterSignature afterWire
          simp [Transform.Frame.replace, Transform.Frame.keep,
            Transform.Frame.localKeep]
          exact congrArg (fun wire => Var.appendRight outer
            (Var.appendRight before wire))
              (supportParallelAppendRightNil afterWire)
    tailTarget := by
      intro signature wire
      apply Var.appendCases (left := outer) (right := before ++ after)
        (motive := fun wire =>
          (Transform.Frame.replace outer before after [] arguments
            ).targetKeep wire = wire)
      · intro inheritedSignature inherited
        simp [Transform.Frame.replace, Transform.Frame.keep]
      · intro localSignature localWire
        apply Var.appendCases (left := before) (right := after)
          (motive := fun localWire' =>
            (Transform.Frame.replace outer before after [] arguments
              ).targetKeep (Var.appendRight outer localWire') =
                Var.appendRight outer localWire')
        · intro beforeSignature beforeWire
          simp [Transform.Frame.replace, Transform.Frame.keep,
            Transform.Frame.localKeep]
        · intro afterSignature afterWire
          simp [Transform.Frame.replace, Transform.Frame.keep,
            Transform.Frame.localKeep]
          exact congrArg (fun wire => Var.appendRight outer
            (Var.appendRight before wire))
              (supportParallelAppendRightNil afterWire)
    retained := by
      intro signature wire
      apply Var.appendCases (left := outer)
        (right := before ++ after)
        (motive := fun wire =>
          ((Transform.Frame.replace outer before
              (.rel arguments :: after) [] arguments).sourceKeep
            ((Transform.Frame.replace outer before after [] arguments
              ).sourceKeep wire)) =
            (Content.Parallel.rootFrame outer before after arguments
              ).targetKeep wire)
      · intro inheritedSignature inherited
        simp [Content.Parallel.rootFrame, Transform.Frame.replace,
          Transform.Frame.keep]
      · intro localSignature localWire
        apply Var.appendCases (left := before) (right := after)
          (motive := fun wire =>
            ((Transform.Frame.replace outer before
                (.rel arguments :: after) [] arguments).sourceKeep
              ((Transform.Frame.replace outer before after [] arguments
                ).sourceKeep (Var.appendRight outer wire))) =
              (Content.Parallel.rootFrame outer before after arguments
                ).targetKeep (Var.appendRight outer wire))
        · intro beforeSignature beforeWire
          simp [Content.Parallel.rootFrame, Transform.Frame.replace,
            Transform.Frame.keep, Transform.Frame.localKeep]
        · intro afterSignature afterWire
          simp [Content.Parallel.rootFrame, Transform.Frame.replace,
            Transform.Frame.keep, Transform.Frame.localKeep]
          change Var.appendRight outer
              (Var.appendRight before (.there (.there afterWire))) =
            Var.appendRight outer
              (Var.appendRight before (.there (.there afterWire)))
          rfl
    first := by
      rfl
    second := by
      simp [Content.Parallel.secondHead, Transform.Frame.replace,
        Transform.Frame.keep, Transform.Frame.localKeep,
        Transform.Frame.insertedHead]
      change Var.appendRight outer (Var.appendRight before (.there .here)) =
        Var.appendRight outer (Var.appendRight before (.there .here))
      rfl
  }

end Structural

end VisualProof.Rule.Completeness.Comprehension
