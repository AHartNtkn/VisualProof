import VisualProof.Diagram.Semantics.Algebra
import VisualProof.Rule.Comprehension.Relation
import VisualProof.Rule.Soundness.Contextual

namespace VisualProof

open Theory
open Diagram

private theorem Var.eq_of_index_eq
    (left right : Var context signature) (equal : left.index = right.index) :
    left = right := by
  induction context with
  | nil => exact nomatch left
  | cons head tail induction =>
      cases left with
      | here =>
          cases right with
          | here => rfl
          | there right =>
              have values := congrArg Fin.val equal
              simp [Var.index] at values
      | there left =>
          cases right with
          | here =>
              have values := congrArg Fin.val equal
              simp [Var.index] at values
          | there right =>
              exact congrArg Var.there (induction left right (by
                apply Fin.ext
                have values := congrArg Fin.val equal
                simpa [Var.index] using values))

private theorem Var.context_get_index
    (wire : Var context signature) : context.get wire.index = signature := by
  induction wire with
  | here => rfl
  | there tail induction => exact induction

private theorem evaluateVars_lookup_get
    (variables : Vars context signatures) (values : Values model context)
    (position : Fin signatures.length) :
    (evaluateVars variables values).lookup (Var.ofIndex position) =
      values.lookup (variables.get position) := by
  induction variables with
  | nil => exact Fin.elim0 position
  | cons head tail induction =>
      exact Fin.cases rfl (fun index => induction index) position

private theorem Diagram.OpenDiagram.external_env_eq_of_boundary
    (pattern : OpenDiagram boundary)
    (left right : Values model pattern.external)
    (equal : evaluateVars pattern.boundaryWire left =
      evaluateVars pattern.boundaryWire right) :
    left = right := by
  apply Values.ext
  intro signature wire
  obtain ⟨position, maps⟩ := pattern.boundarySurjective wire.index
  let boundaryWire := pattern.boundaryWire.get position
  have signatureEq : boundary.get position = signature := by
    calc
      boundary.get position = pattern.external.get boundaryWire.index :=
        (Var.context_get_index boundaryWire).symm
      _ = pattern.external.get wire.index :=
        congrArg (fun index => pattern.external.get index) maps
      _ = signature := Var.context_get_index wire
  subst signature
  have wireEq : boundaryWire = wire := Var.eq_of_index_eq boundaryWire wire maps
  have positionEq := congrArg
    (fun values : Values model boundary =>
      values.lookup (Var.ofIndex position)) equal
  change (evaluateVars pattern.boundaryWire left).lookup
      (Var.ofIndex position) =
    (evaluateVars pattern.boundaryWire right).lookup
      (Var.ofIndex position) at positionEq
  rw [evaluateVars_lookup_get, evaluateVars_lookup_get] at positionEq
  simpa only [boundaryWire, wireEq] using positionEq

/-- Interpret an open pattern as a semantic value of its relation signature. -/
def Diagram.OpenDiagram.asRelation
    (model : Model) (pattern : OpenDiagram arguments) :
    denoteSig model (.rel arguments) :=
  fun values => denoteOpen model pattern values

private theorem denote_singleton_iff
    (item : Item wires) (model : Model) (env : Values model wires) :
    denoteRegion model env (Region.singleton item) ↔
      denoteItem model env item := by
  unfold Region.singleton Region.ofItems
  let appendNil : WireRenaming wires (wires ++ []) :=
    ⟨fun wire => wire.appendLeft []⟩
  change (∃ localEnv : Values model [],
      denoteItemSeq model (env.append localEnv)
        ((ItemSeq.cons item .nil).renameWires appendNil)) ↔ _
  have envEq (localEnv : Values model []) :
      Values.rename appendNil (env.append localEnv) = env := by
    apply Values.ext
    intro signature wire
    simp [appendNil]
  constructor
  · rintro ⟨localEnv, itemDenotes, _⟩
    have renamed := (denoteItem_renameWires model appendNil
      (env.append localEnv) item).mp itemDenotes
    rwa [envEq] at renamed
  · intro itemDenotes
    refine ⟨PUnit.unit, ?_, trivial⟩
    apply (denoteItem_renameWires model appendNil
      (env.append PUnit.unit) item).mpr
    rwa [envEq]


private theorem Rule.Comprehension.Instantiation.Equalities.denote_iff
    (left right : Vars wires signatures)
    (model : Model) (env : Values model wires) :
    denoteRegion model env (Equalities left right) ↔
      evaluateVars left env = evaluateVars right env := by
  induction left with
  | nil =>
      cases right
      change (∃ localEnv : Values model [], True) ↔ PUnit.unit = PUnit.unit
      exact ⟨fun _ => rfl, fun _ => ⟨PUnit.unit, trivial⟩⟩
  | cons head tail induction =>
      cases right with
      | cons other otherTail =>
          rw [Equalities, Region.denote_conjoin, denote_singleton_iff,
            induction]
          simp only [denoteItem_identity, evaluateVars]
          constructor
          · rintro ⟨headDenotes, tailDenotes⟩
            exact Prod.ext (headDenotes 0 1) tailDenotes
          · intro valuesEqual
            have headEqual := congrArg Prod.fst valuesEqual
            have tailEqual := congrArg Prod.snd valuesEqual
            refine ⟨?_, tailEqual⟩
            intro leftPosition rightPosition
            have each (position : Fin 2) :
                env.lookup (equalityPorts head other position) =
                  env.lookup head := by
              refine Fin.cases rfl (fun rest => ?_) position
              simpa [equalityPorts] using headEqual.symm
            exact (each leftPosition).trans (each rightPosition).symm

private theorem Rule.Comprehension.Instantiation.instantiate_denote_iff
    (pattern : OpenDiagram arguments) (ports : Vars targetWires arguments)
    (model : Model) (targetEnv : Values model targetWires) :
    denoteRegion model targetEnv (instantiate pattern ports) ↔
      pattern.asRelation model (evaluateVars ports targetEnv) := by
  rw [instantiate, Region.denote_adjoinAt]
  simp only [denoteItemSeq_nil, true_and]
  constructor
  · rintro ⟨externalEnv, combinedDenotes⟩
    rw [Region.denote_conjoin, denoteRegion_renameWires,
      Equalities.denote_iff] at combinedDenotes
    rcases combinedDenotes with ⟨bodyDenotes, equalitiesDenote⟩
    have renamedEnv : Values.rename
        (⟨fun wire => Var.appendRight targetWires wire⟩ :
          WireRenaming pattern.external (targetWires ++ pattern.external))
        (targetEnv.append externalEnv) = externalEnv := by
      apply Values.ext
      intro signature wire
      simp
    rw [renamedEnv] at bodyDenotes
    have actualEq := evaluateVars_map_eq ports
      (⟨fun wire => wire.appendLeft pattern.external⟩ :
        WireRenaming targetWires (targetWires ++ pattern.external))
      targetEnv (targetEnv.append externalEnv) (fun wire => by simp)
    have boundaryEq := evaluateVars_map_eq pattern.boundaryWire
      (⟨fun wire => Var.appendRight targetWires wire⟩ :
        WireRenaming pattern.external (targetWires ++ pattern.external))
      externalEnv (targetEnv.append externalEnv) (fun wire => by simp)
    exact ⟨externalEnv,
      boundaryEq.symm.trans (equalitiesDenote.symm.trans actualEq),
      bodyDenotes⟩
  · rintro ⟨externalEnv, boundaryDenotes, bodyDenotes⟩
    refine ⟨externalEnv, ?_⟩
    rw [Region.denote_conjoin, denoteRegion_renameWires,
      Equalities.denote_iff]
    have renamedEnv : Values.rename
        (⟨fun wire => Var.appendRight targetWires wire⟩ :
          WireRenaming pattern.external (targetWires ++ pattern.external))
        (targetEnv.append externalEnv) = externalEnv := by
      apply Values.ext
      intro signature wire
      simp
    have actualEq := evaluateVars_map_eq ports
      (⟨fun wire => wire.appendLeft pattern.external⟩ :
        WireRenaming targetWires (targetWires ++ pattern.external))
      targetEnv (targetEnv.append externalEnv) (fun wire => by simp)
    have boundaryEq := evaluateVars_map_eq pattern.boundaryWire
      (⟨fun wire => Var.appendRight targetWires wire⟩ :
        WireRenaming pattern.external (targetWires ++ pattern.external))
      externalEnv (targetEnv.append externalEnv) (fun wire => by simp)
    exact ⟨by rwa [renamedEnv],
      actualEq.trans (boundaryDenotes.symm.trans boundaryEq.symm)⟩

private def Diagram.Values.insertAt
    (before : List Sig) (value : denoteSig model inserted) :
    Values model (before ++ after) →
      Values model (before ++ (inserted :: after)) :=
  match before with
  | [] => fun values => (value, values)
  | _ :: rest => fun values =>
      (values.1, Values.insertAt rest value values.2)

private theorem Rule.Comprehension.localRetain_cons_there
    (head : Sig) (before after arguments : List Sig)
    (wire : Var (before ++ after) signature) :
    localRetain (head :: before) after arguments (.there wire) =
      .there (localRetain before after arguments wire) := by
  apply Var.appendCases
    (motive := fun wire =>
      localRetain (head :: before) after arguments (.there wire) =
        .there (localRetain before after arguments wire))
  · intro signature retained
    calc
      localRetain (head :: before) after arguments
          (Var.there (retained.appendLeft after)) =
        (Var.there retained).appendLeft (.rel arguments :: after) := by
          change localRetain (head :: before) after arguments
              ((Var.there retained).appendLeft after) = _
          simp [localRetain]
      _ = Var.there (localRetain before after arguments
          (retained.appendLeft after)) := by
        simp [localRetain, Var.appendLeft]
  · intro signature trailing
    calc
      localRetain (head :: before) after arguments
          (Var.there (Var.appendRight before trailing)) =
        Var.appendRight (head :: before) (Var.there trailing) := by
          change localRetain (head :: before) after arguments
              (Var.appendRight (head :: before) trailing) = _
          simp [localRetain]
      _ = Var.there (localRetain before after arguments
          (Var.appendRight before trailing)) := by
        simp [localRetain, Var.appendRight]

private theorem Diagram.Values.lookup_insertAt_retain
    (before after : List Sig)
    (value : denoteSig model (.rel arguments))
    (values : Values model (before ++ after))
    (wire : Var (before ++ after) signature) :
    (Values.insertAt before value values).lookup
        (Rule.Comprehension.localRetain before after arguments wire) =
      values.lookup wire := by
  induction before with
  | nil => rfl
  | cons head rest induction =>
      cases values with
      | mk first tail =>
          cases wire with
          | here => rfl
          | there wire =>
              rw [Rule.Comprehension.localRetain_cons_there]
              exact induction tail wire

private theorem Diagram.Values.lookup_insertAt_selected
    (before after : List Sig) (value : denoteSig model inserted)
    (values : Values model (before ++ after)) :
    (Values.insertAt before value values).lookup
        (Var.appendRight before (.here : Var (inserted :: after) inserted)) =
      value := by
  induction before with
  | nil => rfl
  | cons head rest induction =>
      cases values with
      | mk first tail => exact induction tail

private def Rule.Comprehension.Instantiation.Realizes
    (pattern : OpenDiagram arguments)
    (retain : WireRenaming targetWires sourceWires)
    (selected : Var sourceWires (.rel arguments))
    (model : Model) (sourceEnv : Values model sourceWires)
    (targetEnv : Values model targetWires) : Prop :=
  (∀ {signature} (wire : Var targetWires signature),
      sourceEnv.lookup (retain wire) = targetEnv.lookup wire) ∧
    sourceEnv.lookup selected = pattern.asRelation model

private theorem Rule.Comprehension.Instantiation.Realizes.append
    {pattern : OpenDiagram arguments}
    {retain : WireRenaming targetWires sourceWires}
    {selected : Var sourceWires (.rel arguments)}
    {model : Model} {sourceEnv : Values model sourceWires}
    {targetEnv : Values model targetWires}
    (realizes : Realizes pattern retain selected model sourceEnv targetEnv)
    (localEnv : Values model locals) :
    Realizes pattern (retain.appendRight locals)
      (selected.appendLeft locals) model
      (sourceEnv.append localEnv) (targetEnv.append localEnv) := by
  constructor
  · intro signature wire
    apply Var.appendCases
      (motive := fun wire =>
        (sourceEnv.append localEnv).lookup
            (retain.appendRight locals wire) =
          (targetEnv.append localEnv).lookup wire)
    · intro signature inherited
      simpa [WireRenaming.appendRight] using realizes.1 inherited
    · intro signature localWire
      simp [WireRenaming.appendRight]
  · simpa using realizes.2

private theorem Rule.Comprehension.Instantiation.Realizes.ofInserted
    (pattern : OpenDiagram arguments)
    (model : Model) (outerEnv : Values model outer)
    (localEnv : Values model (before ++ after)) :
    Realizes pattern
      (Rule.Comprehension.retain outer before after arguments)
      (Rule.Comprehension.selected outer before after arguments) model
      (outerEnv.append
        (Values.insertAt before (pattern.asRelation model) localEnv))
      (outerEnv.append localEnv) := by
  constructor
  · intro signature wire
    apply Var.appendCases
      (motive := fun wire =>
        (outerEnv.append
          (Values.insertAt before (pattern.asRelation model) localEnv)).lookup
            (Rule.Comprehension.retain outer before after arguments wire) =
          (outerEnv.append localEnv).lookup wire)
    · intro signature inherited
      simp [Rule.Comprehension.retain]
    · intro signature localWire
      simp only [Rule.Comprehension.retain, Var.appendMap_right,
        Values.lookup_append_right]
      exact Values.lookup_insertAt_retain before after
        (pattern.asRelation model) localEnv localWire
  · simp only [Rule.Comprehension.selected, Values.lookup_append_right]
    exact Values.lookup_insertAt_selected before after
      (pattern.asRelation model) localEnv

mutual
  private theorem Rule.Comprehension.Instantiation.RegionResult.sound_iff
      {pattern : OpenDiagram arguments}
      {retain : WireRenaming targetWires sourceWires}
      {selected : Var sourceWires (.rel arguments)}
      {source : Region sourceWires} {target : Region targetWires}
      (step : RegionResult pattern retain selected source target)
      (model : Model) (sourceEnv : Values model sourceWires)
      (targetEnv : Values model targetWires)
      (realizes : Realizes pattern retain selected model sourceEnv targetEnv) :
      denoteRegion model sourceEnv source ↔
        denoteRegion model targetEnv target := by
    cases step with
    | @mk _ _ _ _ locals items result itemsResult =>
      simp only [denoteRegion_mk]
      rw [Region.denote_adjoinAt]
      constructor
      · rintro ⟨localEnv, itemsDenote⟩
        exact ⟨localEnv, trivial,
          (itemsResult.sound_iff model (sourceEnv.append localEnv)
            (targetEnv.append localEnv) (realizes.append localEnv)).mp
              itemsDenote⟩
      · rintro ⟨localEnv, _, resultDenotes⟩
        exact ⟨localEnv,
          (itemsResult.sound_iff model (sourceEnv.append localEnv)
            (targetEnv.append localEnv) (realizes.append localEnv)).mpr
              resultDenotes⟩

  private theorem Rule.Comprehension.Instantiation.ItemsResult.sound_iff
      {pattern : OpenDiagram arguments}
      {retain : WireRenaming targetWires sourceWires}
      {selected : Var sourceWires (.rel arguments)}
      {items : ItemSeq sourceWires} {target : Region targetWires}
      (step : ItemsResult pattern retain selected items target)
      (model : Model) (sourceEnv : Values model sourceWires)
      (targetEnv : Values model targetWires)
      (realizes : Realizes pattern retain selected model sourceEnv targetEnv) :
      denoteItemSeq model sourceEnv items ↔
        denoteRegion model targetEnv target := by
    cases step with
    | nil =>
      change True ↔ ∃ localEnv : Values model [], True
      constructor
      · intro
        exact ⟨PUnit.unit, trivial⟩
      · intro
        trivial
    | cons itemEvidence tailEvidence =>
      rw [denoteItemSeq_cons, Region.denote_conjoin]
      exact and_congr
        (itemEvidence.sound_iff model sourceEnv targetEnv realizes)
        (tailEvidence.sound_iff model sourceEnv targetEnv realizes)

  private theorem Rule.Comprehension.Instantiation.ItemResult.sound_iff
      {pattern : OpenDiagram arguments}
      {retain : WireRenaming targetWires sourceWires}
      {selected : Var sourceWires (.rel arguments)}
      {item : Item sourceWires} {target : Region targetWires}
      (step : ItemResult pattern retain selected item target)
      (model : Model) (sourceEnv : Values model sourceWires)
      (targetEnv : Values model targetWires)
      (realizes : Realizes pattern retain selected model sourceEnv targetEnv) :
      denoteItem model sourceEnv item ↔
        denoteRegion model targetEnv target := by
    cases step with
    | atom head ports =>
      rw [denote_singleton_iff]
      simp only [denoteItem_atom]
      rw [realizes.1 head]
      have argumentsEq := evaluateVars_map_eq ports retain
        targetEnv sourceEnv (fun wire => (realizes.1 wire).symm)
      rw [argumentsEq]
    | selectedAtom ports =>
      rw [instantiate_denote_iff]
      simp only [denoteItem_atom]
      rw [realizes.2]
      have argumentsEq := evaluateVars_map_eq ports retain
        targetEnv sourceEnv (fun wire => (realizes.1 wire).symm)
      rw [argumentsEq]
    | identity signature arity ports =>
      rw [denote_singleton_iff]
      simp only [denoteItem_identity]
      constructor
      · intro sourceDenotes left right
        rw [← realizes.1 (ports left), ← realizes.1 (ports right)]
        exact sourceDenotes left right
      · intro targetDenotes left right
        rw [realizes.1 (ports left), realizes.1 (ports right)]
        exact targetDenotes left right
    | cut bodyEvidence =>
      rw [denote_singleton_iff]
      simp only [denoteItem_cut]
      exact not_congr
        (bodyEvidence.sound_iff model sourceEnv targetEnv realizes)
end

theorem Rule.Comprehension.Instantiates.sound
    {pattern : OpenDiagram arguments} {before after : List Sig}
    {quantified specialized : Region outer}
    (step : Rule.Comprehension.Instantiates pattern before after
      quantified specialized) :
    ∀ (model : Model) (env : Values model outer),
      denoteRegion model env specialized →
        denoteRegion model env quantified := by
  cases step with
  | @mk items result itemsResult =>
      intro model env specializedDenotes
      rw [Region.denote_adjoinAt] at specializedDenotes
      rcases specializedDenotes with ⟨localEnv, _, resultDenotes⟩
      refine ⟨Values.insertAt before (pattern.asRelation model) localEnv, ?_⟩
      exact (Instantiation.ItemsResult.sound_iff itemsResult model
        (env.append
          (Values.insertAt before (pattern.asRelation model) localEnv))
        (env.append localEnv)
        (Instantiation.Realizes.ofInserted pattern model env localEnv)).mpr
          resultDenotes

theorem Rule.Comprehension.Local.sound
    {specialized quantified : Region wires}
    (step : Rule.Comprehension.Local specialized quantified) :
    ∀ (model : Model) (env : Values model wires),
      denoteRegion model env specialized →
        denoteRegion model env quantified := by
  cases step with
  | comprehend arguments before after pattern instantiates =>
      exact instantiates.sound

theorem Rule.Comprehension.sound
    {source target : OpenDiagram boundary}
    (step : Rule.Comprehension source target) :
    ∀ (model : Model) (args : Values model boundary),
      denoteOpen model source args → denoteOpen model target args :=
  Contextual.sound Rule.Comprehension.Local.sound step

end VisualProof
