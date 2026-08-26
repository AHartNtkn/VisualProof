import VisualProof.Diagram.NestedScopedRewrite
import VisualProof.Diagram.Semantics.Algebra
import VisualProof.Diagram.Semantics.ContextReachability

namespace VisualProof.Diagram

open VisualProof.Theory

namespace DiagramContext.WireExtension

/-- A source environment extends one target environment by the distinguished
ancestor-owned wire and gives that wire one fixed value. -/
def Environments
    (retain : WireRenaming targetWires extendedWires)
    (wire : Var extendedWires .iota)
    (targetEnv : Values model targetWires)
    (sourceEnv : Values model extendedWires)
    (wireValue : model.Carrier) : Prop :=
  Values.rename retain sourceEnv = targetEnv ∧
    sourceEnv.lookup wire = wireValue

end DiagramContext.WireExtension

/-- Exact denotational transport through a recursive context extended by one
ancestor-owned wire. Existing frame items see the retained target environment;
the distinguished value remains inherited at the selected descendant. -/
theorem DiagramContext.extendWire_denote_fill_iff
    (context : DiagramContext targetOuter targetWires)
    (sourceOuter : List Sig)
    (outerRetain : WireRenaming targetOuter sourceOuter)
    (outerWire : Var sourceOuter .iota)
    (sourceBody : Region
      (context.extendWire sourceOuter outerRetain outerWire).sourceWires)
    (targetBody : Region targetWires)
    (model : Model)
    (targetEnv : Values model targetOuter)
    (sourceEnv : Values model sourceOuter)
    (wireValue : model.Carrier)
    (outerEnvironments : DiagramContext.WireExtension.Environments
      outerRetain outerWire targetEnv sourceEnv wireValue)
    (bodyIff : ∀
      (targetHoleEnv : Values model targetWires)
      (sourceHoleEnv : Values model
        (context.extendWire sourceOuter outerRetain outerWire).sourceWires),
      DiagramContext.WireExtension.Environments
          (context.extendWire sourceOuter outerRetain outerWire).retain
          (context.extendWire sourceOuter outerRetain outerWire).wire
          targetHoleEnv sourceHoleEnv wireValue →
      context.Reachable targetEnv targetHoleEnv →
        (denoteRegion model sourceHoleEnv sourceBody ↔
          denoteRegion model targetHoleEnv targetBody)) :
    denoteRegion model sourceEnv
        ((context.extendWire sourceOuter outerRetain outerWire).source.fill
          sourceBody) ↔
      denoteRegion model targetEnv (context.fill targetBody) := by
  induction context generalizing sourceOuter with
  | hole =>
      exact bodyIff targetEnv sourceEnv outerEnvironments rfl
  | cut locals before after child induction =>
      let nextRetain := outerRetain.appendRight locals
      let nextWire : Var (sourceOuter ++ locals) .iota :=
        outerWire.appendLeft locals
      let childExtension := child.extendWire (sourceOuter ++ locals)
        nextRetain nextWire
      change denoteRegion model sourceEnv
          (.mk locals
            ((before.renameWires nextRetain).append
              (.cons (.cut (childExtension.source.fill sourceBody))
                (after.renameWires nextRetain)))) ↔
        denoteRegion model targetEnv
          (.mk locals
            (before.append (.cons (.cut (child.fill targetBody)) after)))
      constructor
      · rintro ⟨localEnv, sourceItems⟩
        obtain ⟨sourceBefore, sourceChildNot, sourceAfter⟩ :=
          (denoteItemSeq_frame model (sourceEnv.append localEnv)
            (before.renameWires nextRetain)
            (after.renameWires nextRetain)
            (.cut (childExtension.source.fill sourceBody))).mp sourceItems
        have nextEnvironmentEq :
            Values.rename nextRetain (sourceEnv.append localEnv) =
              targetEnv.append localEnv := by
          apply Values.ext
          intro signature wire
          apply Var.appendCases (left := _) (right := locals)
            (motive := fun wire =>
              (Values.rename nextRetain
                (sourceEnv.append localEnv)).lookup wire =
              (targetEnv.append localEnv).lookup wire)
          · intro inheritedSignature inherited
            have inheritedEq := congrArg
              (fun values => values.lookup inherited) outerEnvironments.1
            simpa [nextRetain, WireRenaming.appendRight] using inheritedEq
          · intro localSignature localWire
            simp [nextRetain, WireRenaming.appendRight]
        have nextWireEq :
            (sourceEnv.append localEnv).lookup nextWire = wireValue := by
          simpa [nextWire] using outerEnvironments.2
        have nextEnvironments :
            DiagramContext.WireExtension.Environments nextRetain nextWire
              (targetEnv.append localEnv) (sourceEnv.append localEnv)
              wireValue :=
          ⟨nextEnvironmentEq, nextWireEq⟩
        have targetBefore :=
          (denoteItemSeq_renameWires model nextRetain
            (sourceEnv.append localEnv) before).mp sourceBefore
        have targetAfter :=
          (denoteItemSeq_renameWires model nextRetain
            (sourceEnv.append localEnv) after).mp sourceAfter
        rw [nextEnvironmentEq] at targetBefore targetAfter
        have childIff := induction
          (sourceOuter := sourceOuter ++ locals)
          (outerRetain := nextRetain) (outerWire := nextWire)
          (sourceBody := sourceBody) (targetBody := targetBody)
          (targetEnv := targetEnv.append localEnv)
          (sourceEnv := sourceEnv.append localEnv)
          nextEnvironments (fun targetHoleEnv sourceHoleEnv environments reachable =>
            bodyIff targetHoleEnv sourceHoleEnv environments
              ⟨localEnv, reachable⟩)
        refine ⟨localEnv, (denoteItemSeq_frame model
          (targetEnv.append localEnv) before after
          (.cut (child.fill targetBody))).mpr
            ⟨targetBefore, ?_, targetAfter⟩⟩
        intro targetChild
        exact sourceChildNot (childIff.mpr targetChild)
      · rintro ⟨localEnv, targetItems⟩
        obtain ⟨targetBefore, targetChildNot, targetAfter⟩ :=
          (denoteItemSeq_frame model (targetEnv.append localEnv)
            before after (.cut (child.fill targetBody))).mp targetItems
        have nextEnvironmentEq :
            Values.rename nextRetain (sourceEnv.append localEnv) =
              targetEnv.append localEnv := by
          apply Values.ext
          intro signature wire
          apply Var.appendCases (left := _) (right := locals)
            (motive := fun wire =>
              (Values.rename nextRetain
                (sourceEnv.append localEnv)).lookup wire =
              (targetEnv.append localEnv).lookup wire)
          · intro inheritedSignature inherited
            have inheritedEq := congrArg
              (fun values => values.lookup inherited) outerEnvironments.1
            simpa [nextRetain, WireRenaming.appendRight] using inheritedEq
          · intro localSignature localWire
            simp [nextRetain, WireRenaming.appendRight]
        have nextWireEq :
            (sourceEnv.append localEnv).lookup nextWire = wireValue := by
          simpa [nextWire] using outerEnvironments.2
        have nextEnvironments :
            DiagramContext.WireExtension.Environments nextRetain nextWire
              (targetEnv.append localEnv) (sourceEnv.append localEnv)
              wireValue :=
          ⟨nextEnvironmentEq, nextWireEq⟩
        have sourceBefore :=
          (denoteItemSeq_renameWires model nextRetain
            (sourceEnv.append localEnv) before).mpr (nextEnvironmentEq ▸ targetBefore)
        have sourceAfter :=
          (denoteItemSeq_renameWires model nextRetain
            (sourceEnv.append localEnv) after).mpr (nextEnvironmentEq ▸ targetAfter)
        have childIff := induction
          (sourceOuter := sourceOuter ++ locals)
          (outerRetain := nextRetain) (outerWire := nextWire)
          (sourceBody := sourceBody) (targetBody := targetBody)
          (targetEnv := targetEnv.append localEnv)
          (sourceEnv := sourceEnv.append localEnv)
          nextEnvironments (fun targetHoleEnv sourceHoleEnv environments reachable =>
            bodyIff targetHoleEnv sourceHoleEnv environments
              ⟨localEnv, reachable⟩)
        refine ⟨localEnv, (denoteItemSeq_frame model
          (sourceEnv.append localEnv)
          (before.renameWires nextRetain)
          (after.renameWires nextRetain)
          (.cut (childExtension.source.fill sourceBody))).mpr
            ⟨sourceBefore, ?_, sourceAfter⟩⟩
        intro sourceChild
        exact targetChildNot (childIff.mp sourceChild)

end VisualProof.Diagram
