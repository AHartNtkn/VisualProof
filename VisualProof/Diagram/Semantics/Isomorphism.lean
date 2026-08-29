import VisualProof.Diagram.Isomorphism
import VisualProof.Diagram.Semantics

namespace VisualProof.Diagram

open VisualProof
open Theory

def EnvironmentsAgree (wire : WireEquiv source target)
    (sourceEnv : Values model source) (targetEnv : Values model target) : Prop :=
  ∀ {signature} (sourceWire : Var source signature),
    sourceEnv.lookup sourceWire = targetEnv.lookup (wire sourceWire)

theorem denoteItemSeq_iff_get
    (model : Model) (env : Values model wires) (items : ItemSeq wires) :
    denoteItemSeq model env items ↔
      ∀ index, denoteItem model env (items.get index) := by
  cases items with
  | nil =>
      constructor
      · intro _ index
        exact Fin.elim0 index
      · intro _
        trivial
  | cons head tail =>
      have induction := denoteItemSeq_iff_get model env tail
      constructor
      · rintro ⟨headDenotes, tailDenotes⟩ index
        exact Fin.cases headDenotes
          (fun tailIndex => induction.mp tailDenotes tailIndex) index
      · intro allDenote
        constructor
        · exact allDenote ⟨0, by simp [ItemSeq.length]⟩
        · apply induction.mpr
          intro index
          exact allDenote index.succ

private def RegionDenotationMotive
    {sourceOuter targetOuter : List Sig}
    (ambient : WireEquiv sourceOuter targetOuter)
    (source : Region sourceOuter) (target : Region targetOuter)
    (_ : RegionIso ambient source target) : Prop :=
  ∀ (model : Model)
    (sourceEnv : Values model sourceOuter)
    (targetEnv : Values model targetOuter),
    EnvironmentsAgree ambient sourceEnv targetEnv →
      (denoteRegion model sourceEnv source ↔
        denoteRegion model targetEnv target)

private def ItemDenotationMotive
    {sourceWires targetWires : List Sig}
    (ambient : WireEquiv sourceWires targetWires)
    (source : Item sourceWires) (target : Item targetWires)
    (_ : ItemIso ambient source target) : Prop :=
  ∀ (model : Model)
    (sourceEnv : Values model sourceWires)
    (targetEnv : Values model targetWires),
    EnvironmentsAgree ambient sourceEnv targetEnv →
      (denoteItem model sourceEnv source ↔
        denoteItem model targetEnv target)

private def ItemsDenotationMotive
    {sourceWires targetWires : List Sig}
    (ambient : WireEquiv sourceWires targetWires)
    (source : ItemSeq sourceWires) (target : ItemSeq targetWires)
    (_ : ItemSeqIso ambient source target) : Prop :=
  ∀ (model : Model)
    (sourceEnv : Values model sourceWires)
    (targetEnv : Values model targetWires),
    EnvironmentsAgree ambient sourceEnv targetEnv →
      (denoteItemSeq model sourceEnv source ↔
        denoteItemSeq model targetEnv target)

private theorem appendEnvironmentsAgree
    (ambient : WireEquiv sourceOuter targetOuter)
    (locals : WireEquiv sourceLocals targetLocals)
    (sourceOuterEnv : Values model sourceOuter)
    (targetOuterEnv : Values model targetOuter)
    (sourceLocalEnv : Values model sourceLocals)
    (targetLocalEnv : Values model targetLocals)
    (outerAgree : EnvironmentsAgree ambient sourceOuterEnv targetOuterEnv)
    (localAgree : EnvironmentsAgree locals sourceLocalEnv targetLocalEnv) :
    EnvironmentsAgree (ambient.append locals)
      (sourceOuterEnv.append sourceLocalEnv)
      (targetOuterEnv.append targetLocalEnv) := by
  intro signature wire
  apply Var.appendCases
    (motive := fun wire =>
      (sourceOuterEnv.append sourceLocalEnv).lookup wire =
        (targetOuterEnv.append targetLocalEnv).lookup
          (ambient.append locals wire))
  · intro signature inherited
    simpa only [Values.lookup_append_left, WireEquiv.append_apply_left] using
      outerAgree inherited
  · intro signature localWire
    simpa only [Values.lookup_append_right, WireEquiv.append_apply_right] using
      localAgree localWire

private theorem regionDenotationCase
    {sourceOuter targetOuter sourceLocals targetLocals : List Sig}
    {ambient : WireEquiv sourceOuter targetOuter}
    {sourceItems : ItemSeq (sourceOuter ++ sourceLocals)}
    {targetItems : ItemSeq (targetOuter ++ targetLocals)}
    (locals : WireEquiv sourceLocals targetLocals)
    (items : ItemSeqIso (ambient.append locals) sourceItems targetItems)
    (itemsIH : ItemsDenotationMotive
      (ambient.append locals) sourceItems targetItems items) :
    RegionDenotationMotive ambient (.mk sourceLocals sourceItems)
      (.mk targetLocals targetItems) (.mk locals items) := by
  intro model sourceEnv targetEnv outerAgree
  constructor
  · rintro ⟨sourceLocalEnv, sourceDenotes⟩
    let targetLocalEnv := Values.rename locals.invRenaming sourceLocalEnv
    refine ⟨targetLocalEnv, (itemsIH model
      (sourceEnv.append sourceLocalEnv)
      (targetEnv.append targetLocalEnv) ?_).mp sourceDenotes⟩
    apply appendEnvironmentsAgree ambient locals
    · exact outerAgree
    · intro signature wire
      simp only [targetLocalEnv, Values.lookup_rename]
      rw [locals.left_inv]
  · rintro ⟨targetLocalEnv, targetDenotes⟩
    let sourceLocalEnv := Values.rename locals.toRenaming targetLocalEnv
    refine ⟨sourceLocalEnv, (itemsIH model
      (sourceEnv.append sourceLocalEnv)
      (targetEnv.append targetLocalEnv) ?_).mpr targetDenotes⟩
    apply appendEnvironmentsAgree ambient locals
    · exact outerAgree
    · intro signature wire
      simp only [sourceLocalEnv, Values.lookup_rename]

private theorem atomDenotationCase
    {sourceWires targetWires arguments : List Sig}
    {ambient : WireEquiv sourceWires targetWires}
    {sourceHead : Var sourceWires (.rel arguments)}
    {targetHead : Var targetWires (.rel arguments)}
    {sourcePorts : Vars sourceWires arguments}
    {targetPorts : Vars targetWires arguments}
    (head_eq : ambient sourceHead = targetHead)
    (ports_eq : sourcePorts.map (fun wire => ambient wire) = targetPorts) :
    ItemDenotationMotive ambient (.atom sourceHead sourcePorts)
      (.atom targetHead targetPorts) (.atom head_eq ports_eq) := by
  intro model sourceEnv targetEnv agree
  subst targetHead
  subst targetPorts
  simp only [denoteItem_atom]
  rw [← agree sourceHead]
  have argumentsEq :
      evaluateVars (sourcePorts.map (fun wire => ambient wire)) targetEnv =
        evaluateVars sourcePorts sourceEnv := by
    exact evaluateVars_map_eq sourcePorts ambient.toRenaming
      sourceEnv targetEnv agree
  rw [argumentsEq]

private theorem identityDenotationCase
    {sourceWires targetWires : List Sig} {signature : Sig} {arity : Nat}
    {ambient : WireEquiv sourceWires targetWires}
    {sourcePorts : Fin arity → Var sourceWires signature}
    {targetPorts : Fin arity → Var targetWires signature}
    (positions : FiniteEquiv (Fin arity) (Fin arity))
    (ports_eq : ∀ sourceIndex,
      ambient (sourcePorts sourceIndex) =
        targetPorts (positions sourceIndex)) :
    ItemDenotationMotive ambient (.identity signature arity sourcePorts)
      (.identity signature arity targetPorts) (.identity positions ports_eq) := by
  intro model sourceEnv targetEnv agree
  simp only [denoteItem_identity]
  constructor
  · intro sourceDenotes targetLeft targetRight
    let sourceLeft := positions.symm targetLeft
    let sourceRight := positions.symm targetRight
    rw [← positions.apply_symm_apply targetLeft,
      ← positions.apply_symm_apply targetRight,
      ← ports_eq sourceLeft, ← ports_eq sourceRight,
      ← agree (sourcePorts sourceLeft), ← agree (sourcePorts sourceRight)]
    exact sourceDenotes sourceLeft sourceRight
  · intro targetDenotes sourceLeft sourceRight
    rw [agree (sourcePorts sourceLeft), agree (sourcePorts sourceRight),
      ports_eq sourceLeft, ports_eq sourceRight]
    exact targetDenotes (positions sourceLeft) (positions sourceRight)

private theorem termDenotationCase
    {sourceWires targetWires : List Sig} {freeArity : Nat}
    {ambient : WireEquiv sourceWires targetWires}
    {sourceOutput : Var sourceWires .iota}
    {targetOutput : Var targetWires .iota}
    {sourcePorts : Fin freeArity → Var sourceWires .iota}
    {targetPorts : Fin freeArity → Var targetWires .iota}
    {lambdaTerm : Lambda.Term 0 (Fin freeArity)}
    (outputEq : ambient sourceOutput = targetOutput)
    (portsEq : ∀ slot,
      ambient (sourcePorts slot) = targetPorts slot) :
    ItemDenotationMotive ambient
      (.term sourceOutput freeArity sourcePorts lambdaTerm)
      (.term targetOutput freeArity targetPorts lambdaTerm)
      (.term outputEq portsEq) := by
  intro model sourceEnv targetEnv agree
  simp only [denoteItem_term]
  have evalEq :
      model.eval lambdaTerm (fun slot => sourceEnv.lookup (sourcePorts slot)) =
        model.eval lambdaTerm (fun slot => targetEnv.lookup (targetPorts slot)) := by
    apply congrArg (model.eval lambdaTerm)
    funext slot
    rw [agree (sourcePorts slot), portsEq slot]
  rw [agree sourceOutput, outputEq, evalEq]

private theorem cutDenotationCase
    {sourceWires targetWires : List Sig}
    {ambient : WireEquiv sourceWires targetWires}
    {sourceBody : Region sourceWires} {targetBody : Region targetWires}
    (body : RegionIso ambient sourceBody targetBody)
    (bodyIH : RegionDenotationMotive ambient sourceBody targetBody body) :
    ItemDenotationMotive ambient (.cut sourceBody) (.cut targetBody)
      (.cut body) := by
  intro model sourceEnv targetEnv agree
  simp only [denoteItem_cut]
  exact not_congr (bodyIH model sourceEnv targetEnv agree)

private theorem permuteDenotationCase
    {sourceWires targetWires : List Sig}
    {ambient : WireEquiv sourceWires targetWires}
    {source : ItemSeq sourceWires} {target : ItemSeq targetWires}
    (positions : FiniteEquiv (Fin source.length) (Fin target.length))
    (items : ∀ (sourceIndex : Fin source.length)
      (targetIndex : Fin target.length), positions sourceIndex = targetIndex →
      ItemIso ambient (source.get sourceIndex) (target.get targetIndex))
    (itemsIH : ∀ (sourceIndex : Fin source.length)
      (targetIndex : Fin target.length) (equality : positions sourceIndex = targetIndex),
      ItemDenotationMotive ambient (source.get sourceIndex)
        (target.get targetIndex) (items sourceIndex targetIndex equality)) :
    ItemsDenotationMotive ambient source target (.permute positions items) := by
  intro model sourceEnv targetEnv agree
  rw [denoteItemSeq_iff_get, denoteItemSeq_iff_get]
  constructor
  · intro sourceDenotes targetIndex
    let sourceIndex := positions.invFun targetIndex
    have positionEq : positions sourceIndex = targetIndex :=
      positions.right_inv targetIndex
    exact (itemsIH sourceIndex targetIndex positionEq model
      sourceEnv targetEnv agree).mp (sourceDenotes sourceIndex)
  · intro targetDenotes sourceIndex
    exact (itemsIH sourceIndex (positions sourceIndex) rfl model
      sourceEnv targetEnv agree).mpr (targetDenotes (positions sourceIndex))

private theorem regionDenotationRec
    {ambient : WireEquiv sourceWires targetWires}
    {source : Region sourceWires} {target : Region targetWires}
    (iso : RegionIso ambient source target) :
    RegionDenotationMotive ambient source target iso := by
  apply RegionIso.rec
    (motive_1 := RegionDenotationMotive)
    (motive_2 := ItemDenotationMotive)
    (motive_3 := ItemsDenotationMotive)
    regionDenotationCase atomDenotationCase identityDenotationCase termDenotationCase
    cutDenotationCase permuteDenotationCase iso

private theorem itemDenotationRec
    {ambient : WireEquiv sourceWires targetWires}
    {source : Item sourceWires} {target : Item targetWires}
    (iso : ItemIso ambient source target) :
    ItemDenotationMotive ambient source target iso := by
  apply ItemIso.rec
    (motive_1 := RegionDenotationMotive)
    (motive_2 := ItemDenotationMotive)
    (motive_3 := ItemsDenotationMotive)
    regionDenotationCase atomDenotationCase identityDenotationCase termDenotationCase
    cutDenotationCase permuteDenotationCase iso

private theorem itemsDenotationRec
    {ambient : WireEquiv sourceWires targetWires}
    {source : ItemSeq sourceWires} {target : ItemSeq targetWires}
    (iso : ItemSeqIso ambient source target) :
    ItemsDenotationMotive ambient source target iso := by
  apply ItemSeqIso.rec
    (motive_1 := RegionDenotationMotive)
    (motive_2 := ItemDenotationMotive)
    (motive_3 := ItemsDenotationMotive)
    regionDenotationCase atomDenotationCase identityDenotationCase termDenotationCase
    cutDenotationCase permuteDenotationCase iso

theorem RegionIso.denotation
    {ambient : WireEquiv sourceWires targetWires}
    {source : Region sourceWires} {target : Region targetWires}
    (iso : RegionIso ambient source target)
    (model : Model) (sourceEnv : Values model sourceWires)
    (targetEnv : Values model targetWires)
    (agree : EnvironmentsAgree ambient sourceEnv targetEnv) :
    denoteRegion model sourceEnv source ↔ denoteRegion model targetEnv target :=
  regionDenotationRec iso model sourceEnv targetEnv agree

theorem ItemIso.denotation
    {ambient : WireEquiv sourceWires targetWires}
    {source : Item sourceWires} {target : Item targetWires}
    (iso : ItemIso ambient source target)
    (model : Model) (sourceEnv : Values model sourceWires)
    (targetEnv : Values model targetWires)
    (agree : EnvironmentsAgree ambient sourceEnv targetEnv) :
    denoteItem model sourceEnv source ↔ denoteItem model targetEnv target :=
  itemDenotationRec iso model sourceEnv targetEnv agree

theorem ItemSeqIso.denotation
    {ambient : WireEquiv sourceWires targetWires}
    {source : ItemSeq sourceWires} {target : ItemSeq targetWires}
    (iso : ItemSeqIso ambient source target)
    (model : Model) (sourceEnv : Values model sourceWires)
    (targetEnv : Values model targetWires)
    (agree : EnvironmentsAgree ambient sourceEnv targetEnv) :
    denoteItemSeq model sourceEnv source ↔ denoteItemSeq model targetEnv target :=
  itemsDenotationRec iso model sourceEnv targetEnv agree

end VisualProof.Diagram
