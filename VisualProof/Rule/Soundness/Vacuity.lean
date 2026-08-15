import VisualProof.Diagram.Semantics.Algebra
import VisualProof.Diagram.Semantics.UnaryIdentity
import VisualProof.Rule.Vacuity
import VisualProof.Rule.Soundness.Contextual

namespace VisualProof.Rule

open Theory
open Diagram

namespace Vacuity

private theorem denoteItem_nullary_identity
    (model : Model) (env : Values model wires) (signature : Sig) :
    denoteItem model env (.identity signature 0 Fin.elim0) := by
  intro left
  exact Fin.elim0 left

private theorem Point.denote_present_iff
    (locals : List Sig) (items : ItemSeq (outer ++ locals))
    (signature : Sig) (model : Model) (env : Values model outer) :
    denoteRegion model env (Point.present locals items signature) ↔
      denoteRegion model env (Point.plain locals items) := by
  simp only [Point.present, Point.plain, denoteRegion_mk]
  constructor
  · rintro ⟨localEnv, presentDenotes⟩
    exact ⟨localEnv, (denoteItemSeq_append model (env.append localEnv)
      items _).mp presentDenotes |>.1⟩
  · rintro ⟨localEnv, plainDenotes⟩
    refine ⟨localEnv, (denoteItemSeq_append model (env.append localEnv)
      items _).mpr ⟨plainDenotes, ?_⟩⟩
    exact ⟨denoteItem_nullary_identity model (env.append localEnv) signature,
      trivial⟩

private theorem Pin.denote_present_iff
    (locals : List Sig) (items : ItemSeq (outer ++ locals))
    (signature : Sig) (wire : Var (outer ++ locals) signature)
    (model : Model) (env : Values model outer) :
    denoteRegion model env (Pin.present locals items signature wire) ↔
      denoteRegion model env (Pin.plain locals items) := by
  simp only [Pin.present, Pin.plain, denoteRegion_mk]
  constructor
  · rintro ⟨localEnv, presentDenotes⟩
    exact ⟨localEnv, (denoteItemSeq_append model (env.append localEnv)
      items _).mp presentDenotes |>.1⟩
  · rintro ⟨localEnv, plainDenotes⟩
    refine ⟨localEnv, (denoteItemSeq_append model (env.append localEnv)
      items _).mpr ⟨plainDenotes, ?_⟩⟩
    exact ⟨denoteItem_unary_identity model (env.append localEnv) wire, trivial⟩

private theorem DiagramContext.denote_fill_iff
    (context : DiagramContext outer holeWires)
    (before after : Region holeWires)
    (localIff : ∀ env : Values model holeWires,
      denoteRegion model env before ↔ denoteRegion model env after)
    (env : Values model outer) :
    denoteRegion model env (context.fill before) ↔
      denoteRegion model env (context.fill after) := by
  cases polarity : context.polarity with
  | positive =>
      constructor
      · have implication := context.denote_fill model before after
          (fun holeEnv => (localIff holeEnv).mp) env
        rw [polarity] at implication
        exact implication
      · have implication := context.denote_fill model after before
          (fun holeEnv => (localIff holeEnv).mpr) env
        rw [polarity] at implication
        exact implication
  | negative =>
      constructor
      · have implication := context.denote_fill model after before
          (fun holeEnv => (localIff holeEnv).mpr) env
        rw [polarity] at implication
        exact implication
      · have implication := context.denote_fill model before after
          (fun holeEnv => (localIff holeEnv).mp) env
        rw [polarity] at implication
        exact implication

private theorem Stub.Far.denote_result_iff
    {wire : Var baseWires signature} {items : ItemSeq baseWires}
    (far : Stub.Far wire items) (model : Model)
    (env : Values model baseWires) :
    denoteItemSeq model env far.result ↔ denoteItemSeq model env items := by
  cases far with
  | atBase =>
      simp only [Stub.Far.result, denoteItemSeq_append]
      constructor
      · exact fun present => present.1
      · intro plain
        exact ⟨plain, ⟨denoteItem_unary_identity model env wire, trivial⟩⟩
  | below before after focus descendant farLocals farItems bodyEq =>
      subst items
      simp only [Stub.Far.result]
      rw [denoteItemSeq_frame, denoteItemSeq_frame]
      have childIff := DiagramContext.denote_fill_iff descendant
        (Pin.present farLocals farItems signature
          ((descendant.outerWire wire).appendLeft farLocals))
        (Pin.plain farLocals farItems)
        (fun holeEnv => Pin.denote_present_iff farLocals farItems signature
          ((descendant.outerWire wire).appendLeft farLocals) model holeEnv) env
      simp only [Pin.present, Pin.plain] at childIff
      simp only [denoteItem_cut]
      rw [not_congr childIff, bodyEq]

private noncomputable def arbitraryValue (model : Model) :
    (signature : Sig) → denoteSig model signature
  | .iota => Classical.choice model.nonempty
  | .rel _ => fun _ => False

private def singletonValue (value : denoteSig model signature) :
    Values model [signature] :=
  (value, PUnit.unit)

private theorem Stub.hostValues
    (outerEnv : Values model outer) (hostEnv : Values model hostLocals)
    (value : denoteSig model signature) :
    Values.rename (Stub.hostRename outer hostLocals signature)
        (outerEnv.append (hostEnv.append (singletonValue value))) =
      outerEnv.append hostEnv := by
  apply Values.ext
  intro wireSignature wire
  apply Var.appendCases (motive := fun wire =>
    (Values.rename (Stub.hostRename outer hostLocals signature)
      (outerEnv.append (hostEnv.append (singletonValue value)))).lookup wire =
        (outerEnv.append hostEnv).lookup wire)
  · intro inheritedSignature inherited
    simp [Stub.hostRename, Region.adjoinHostWire, Region.conjoinLeftWire]
  · intro localSignature localWire
    simp [Stub.hostRename, Region.adjoinHostWire, Region.conjoinLeftWire]

private noncomputable def Stub.freshValue (model : Model)
    (env : Values model (outer ++ hostLocals))
    (signature : Sig) (arity : Nat)
    (ports : Fin arity → Var (outer ++ hostLocals) signature) :
    denoteSig model signature :=
  match arity with
  | 0 => arbitraryValue model signature
  | _ + 1 => env.lookup (ports 0)

private theorem Stub.freshValue_eq_port
    (model : Model) (env : Values model (outer ++ hostLocals))
    (signature : Sig) (arity : Nat)
    (ports : Fin arity → Var (outer ++ hostLocals) signature)
    (identityDenotes : denoteItem model env
      (.identity signature arity ports)) (index : Fin arity) :
    Stub.freshValue model env signature arity ports = env.lookup (ports index) := by
  cases arity with
  | zero => exact Fin.elim0 index
  | succ arity =>
      exact identityDenotes 0 index

private theorem Stub.extendedIdentity_denotes_iff
    (outerEnv : Values model outer) (hostEnv : Values model hostLocals)
    (signature : Sig) (arity : Nat)
    (ports : Fin arity → Var (outer ++ hostLocals) signature)
    (position : Fin (arity + 1)) :
    let baseEnv := outerEnv.append hostEnv
    let fresh := Stub.freshValue model baseEnv signature arity ports
    let combinedEnv := outerEnv.append
      (hostEnv.append (singletonValue fresh))
    denoteItem model combinedEnv
        (.identity signature (arity + 1)
          (Stub.insertPort position (Stub.freshWire outer hostLocals signature)
            (fun index => Stub.hostRename outer hostLocals signature
              (ports index)))) ↔
      denoteItem model baseEnv (.identity signature arity ports) := by
  dsimp only
  let baseEnv := outerEnv.append hostEnv
  let fresh := Stub.freshValue model baseEnv signature arity ports
  let combinedEnv := outerEnv.append
    (hostEnv.append (singletonValue fresh))
  have hostEq := Stub.hostValues outerEnv hostEnv fresh
  have renamedLookup (index : Fin arity) :
      combinedEnv.lookup (Stub.hostRename outer hostLocals signature
        (ports index)) = baseEnv.lookup (ports index) := by
    have := congrArg (fun values => values.lookup (ports index)) hostEq
    simpa only [Values.lookup_rename] using this
  have freshLookup : combinedEnv.lookup
      (Stub.freshWire outer hostLocals signature) = fresh := by
    simp [combinedEnv, Stub.freshWire, singletonValue, Values.lookup]
  have positionLe : position.val ≤
      (List.ofFn fun index =>
        Stub.hostRename outer hostLocals signature (ports index)).length := by
    simp
    omega
  have retainedIndex (index : Fin arity) :
      ∃ lifted : Fin (arity + 1),
        Stub.insertPort position (Stub.freshWire outer hostLocals signature)
          (fun index => Stub.hostRename outer hostLocals signature
            (ports index)) lifted =
          Stub.hostRename outer hostLocals signature (ports index) := by
    have retained : Stub.hostRename outer hostLocals signature (ports index) ∈
        (List.ofFn (fun index =>
          Stub.hostRename outer hostLocals signature (ports index))).insertIdx
            position.val (Stub.freshWire outer hostLocals signature) :=
      (List.mem_insertIdx positionLe).mpr
        (Or.inr ((List.mem_ofFn).mpr ⟨index, rfl⟩))
    rw [← Stub.ofFn_insertPort] at retained
    exact (List.mem_ofFn).mp retained
  constructor
  · intro extended left right
    obtain ⟨leftLifted, leftEq⟩ := retainedIndex left
    obtain ⟨rightLifted, rightEq⟩ := retainedIndex right
    have equality := extended leftLifted rightLifted
    rw [leftEq, rightEq, renamedLookup, renamedLookup] at equality
    exact equality
  · intro original left right
    have valueAt (index : Fin (arity + 1)) :
        combinedEnv.lookup
            (Stub.insertPort position (Stub.freshWire outer hostLocals signature)
              (fun index => Stub.hostRename outer hostLocals signature
                (ports index)) index) = fresh := by
      have member : Stub.insertPort position
          (Stub.freshWire outer hostLocals signature)
          (fun index => Stub.hostRename outer hostLocals signature
            (ports index)) index ∈
          List.ofFn (Stub.insertPort position
            (Stub.freshWire outer hostLocals signature)
            (fun index => Stub.hostRename outer hostLocals signature
              (ports index))) :=
        (List.mem_ofFn).mpr ⟨index, rfl⟩
      rw [Stub.ofFn_insertPort] at member
      rcases (List.mem_insertIdx positionLe).mp member with freshEq | retained
      · rw [freshEq, freshLookup]
      · obtain ⟨retainedIndex, retainedEq⟩ := (List.mem_ofFn).mp retained
        rw [← retainedEq, renamedLookup]
        exact (Stub.freshValue_eq_port model baseEnv signature arity ports
          original retainedIndex).symm
    exact (valueAt left).trans (valueAt right).symm

private theorem Stub.denote_extendedItems_iff
    (hostLocals : List Sig)
    (before after : ItemSeq (outer ++ hostLocals))
    (signature : Sig) (arity : Nat)
    (ports : Fin arity → Var (outer ++ hostLocals) signature)
    (position : Fin (arity + 1))
    (model : Model) (outerEnv : Values model outer)
    (hostEnv : Values model hostLocals) :
    let baseEnv := outerEnv.append hostEnv
    let fresh := Stub.freshValue model baseEnv signature arity ports
    let combinedEnv := outerEnv.append
      (hostEnv.append (singletonValue fresh))
    denoteItemSeq model combinedEnv
        (Stub.extendedItems hostLocals before after signature arity ports position) ↔
      denoteItemSeq model baseEnv
        (before.append (.cons (.identity signature arity ports) after)) := by
  dsimp only
  let baseEnv := outerEnv.append hostEnv
  let fresh := Stub.freshValue model baseEnv signature arity ports
  let combinedEnv := outerEnv.append
    (hostEnv.append (singletonValue fresh))
  have hostEq := Stub.hostValues outerEnv hostEnv fresh
  have identityIff := Stub.extendedIdentity_denotes_iff outerEnv hostEnv
    signature arity ports position
  dsimp only at identityIff
  simp only [Stub.extendedItems, denoteItemSeq_frame]
  rw [denoteItemSeq_renameWires, denoteItemSeq_renameWires,
    hostEq, identityIff]

private theorem Stub.extendedIdentity_to_plain
    (outerEnv : Values model outer) (hostEnv : Values model hostLocals)
    (value : denoteSig model signature)
    (arity : Nat)
    (ports : Fin arity → Var (outer ++ hostLocals) signature)
    (position : Fin (arity + 1))
    (extended : denoteItem model
      (outerEnv.append (hostEnv.append (singletonValue value)))
      (.identity signature (arity + 1)
        (Stub.insertPort position (Stub.freshWire outer hostLocals signature)
          (fun index => Stub.hostRename outer hostLocals signature
            (ports index))))) :
    denoteItem model (outerEnv.append hostEnv)
      (.identity signature arity ports) := by
  have hostEq := Stub.hostValues outerEnv hostEnv value
  have positionLe : position.val ≤
      (List.ofFn fun index =>
        Stub.hostRename outer hostLocals signature (ports index)).length := by
    simp
    omega
  have retainedIndex (index : Fin arity) :
      ∃ lifted : Fin (arity + 1),
        Stub.insertPort position (Stub.freshWire outer hostLocals signature)
          (fun index => Stub.hostRename outer hostLocals signature
            (ports index)) lifted =
          Stub.hostRename outer hostLocals signature (ports index) := by
    have retained : Stub.hostRename outer hostLocals signature (ports index) ∈
        (List.ofFn (fun index =>
          Stub.hostRename outer hostLocals signature (ports index))).insertIdx
            position.val (Stub.freshWire outer hostLocals signature) :=
      (List.mem_insertIdx positionLe).mpr
        (Or.inr ((List.mem_ofFn).mpr ⟨index, rfl⟩))
    rw [← Stub.ofFn_insertPort] at retained
    exact (List.mem_ofFn).mp retained
  intro left right
  obtain ⟨leftLifted, leftEq⟩ := retainedIndex left
  obtain ⟨rightLifted, rightEq⟩ := retainedIndex right
  have equality := extended leftLifted rightLifted
  rw [leftEq, rightEq] at equality
  have leftEq := congrArg (fun values => values.lookup (ports left)) hostEq
  have rightEq := congrArg (fun values => values.lookup (ports right)) hostEq
  simp only [Values.lookup_rename] at leftEq rightEq
  exact leftEq.symm.trans (equality.trans rightEq)

private theorem Stub.denote_extendedItems_to_plain
    (hostLocals : List Sig)
    (before after : ItemSeq (outer ++ hostLocals))
    (signature : Sig) (arity : Nat)
    (ports : Fin arity → Var (outer ++ hostLocals) signature)
    (position : Fin (arity + 1))
    (model : Model) (outerEnv : Values model outer)
    (hostEnv : Values model hostLocals)
    (value : denoteSig model signature)
    (extended : denoteItemSeq model
      (outerEnv.append (hostEnv.append (singletonValue value)))
      (Stub.extendedItems hostLocals before after signature arity ports position)) :
    denoteItemSeq model (outerEnv.append hostEnv)
      (before.append (.cons (.identity signature arity ports) after)) := by
  have hostEq := Stub.hostValues outerEnv hostEnv value
  simp only [Stub.extendedItems, denoteItemSeq_frame] at extended ⊢
  rcases extended with ⟨beforeDenotes, identityDenotes, afterDenotes⟩
  have beforePlain := (denoteItemSeq_renameWires model
    (Stub.hostRename outer hostLocals signature)
    (outerEnv.append (hostEnv.append (singletonValue value))) before).mp
      beforeDenotes
  have afterPlain := (denoteItemSeq_renameWires model
    (Stub.hostRename outer hostLocals signature)
    (outerEnv.append (hostEnv.append (singletonValue value))) after).mp
      afterDenotes
  rw [hostEq] at beforePlain afterPlain
  exact ⟨beforePlain,
    Stub.extendedIdentity_to_plain outerEnv hostEnv value arity ports position
      identityDenotes,
    afterPlain⟩

private theorem Values.exists_append
    (values : Values model (left ++ right)) :
    ∃ (leftValues : Values model left) (rightValues : Values model right),
      leftValues.append rightValues = values := by
  induction left with
  | nil => exact ⟨PUnit.unit, values, rfl⟩
  | cons signature rest induction =>
      rcases values with ⟨head, tail⟩
      rcases induction tail with ⟨leftValues, rightValues, equality⟩
      refine ⟨(head, leftValues), rightValues, ?_⟩
      simp only [Values.append]
      rw [equality]

private theorem Stub.denote_present_iff
    (hostLocals : List Sig)
    (before after : ItemSeq (outer ++ hostLocals))
    (signature : Sig) (arity : Nat)
    (ports : Fin arity → Var (outer ++ hostLocals) signature)
    (position : Fin (arity + 1))
    (far : Stub.Far (Stub.freshWire outer hostLocals signature)
      (Stub.extendedItems hostLocals before after signature arity ports position))
    (model : Model) (env : Values model outer) :
    denoteRegion model env
        (Stub.present hostLocals before after signature arity ports position far) ↔
      denoteRegion model env
        (Stub.plain hostLocals before after signature arity ports) := by
  simp only [Stub.present, Stub.plain, denoteRegion_mk]
  constructor
  · rintro ⟨combinedEnv, resultDenotes⟩
    rcases Values.exists_append (left := hostLocals) (right := [signature])
      combinedEnv with ⟨hostEnv, lastEnv, combinedEq⟩
    rcases lastEnv with ⟨value, tailUnit⟩
    cases tailUnit
    subst combinedEnv
    have extendedDenotes :=
      (far.denote_result_iff model
        (env.append (hostEnv.append (singletonValue value)))).mp resultDenotes
    exact ⟨hostEnv, Stub.denote_extendedItems_to_plain hostLocals before after
      signature arity ports position model env hostEnv value extendedDenotes⟩
  · rintro ⟨hostEnv, plainDenotes⟩
    let baseEnv := env.append hostEnv
    let fresh := Stub.freshValue model baseEnv signature arity ports
    let combinedEnv := env.append (hostEnv.append (singletonValue fresh))
    have extendedDenotes := (Stub.denote_extendedItems_iff hostLocals before after
      signature arity ports position model env hostEnv).mpr plainDenotes
    exact ⟨hostEnv.append (singletonValue fresh),
      (far.denote_result_iff model combinedEnv).mpr extendedDenotes⟩

theorem Local.sound_iff
    {before after : Region wires} (step : Local before after)
    (model : Model) (env : Values model wires) :
    denoteRegion model env before ↔ denoteRegion model env after := by
  cases step with
  | point locals items signature =>
      exact (Point.denote_present_iff locals items signature model env).symm
  | stub hostLocals before after signature arity ports position far =>
      exact (Stub.denote_present_iff hostLocals before after signature arity ports
        position far model env).symm
  | pin locals items signature wire =>
      exact (Pin.denote_present_iff locals items signature wire model env).symm

end Vacuity

theorem Vacuity.sound
    {source target : OpenDiagram boundary}
    (step : Vacuity source target) :
    ∀ (model : Model) (args : Values model boundary),
      denoteOpen model source args → denoteOpen model target args := by
  apply Contextual.sound (step := step)
  intro wires before after localStep model env
  rcases localStep with forward | backward
  · exact (Vacuity.Local.sound_iff forward model env).mp
  · exact (Vacuity.Local.sound_iff backward model env).mpr

end VisualProof.Rule
