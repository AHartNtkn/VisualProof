import VisualProof.Rule.WirePrimitive.Leaves
import VisualProof.Rule.WirePrimitive.Partition

namespace VisualProof

namespace WirePrimitive

namespace LeavesFixtures

open ConcreteWirePrimitive
open Leaves

private def idx {bound : Nat}
    (value : Nat) (valid : value < bound := by native_decide) : Fin bound :=
  ⟨value, valid⟩

private def leafError? {α : Type} :
    Except WireLeafError α → Option WireLeafError
  | .error error => some error
  | .ok _ => none

/-!
The formal corpus has one application at the acted root and one below two
cuts.  Each site has a distinct formal head wire, so acceptance proves that
the rule is per-site rather than accidentally uniform-head.
-/
private def formalRaw : ConcreteDiagram 0 where
  regionCount := 3
  nodeCount := 2
  wireCount := 5
  root := 0
  regions
    | ⟨0, _⟩ => .sheet
    | ⟨1, _⟩ => .cut 0
    | ⟨2, _⟩ => .cut 1
  nodes
    | ⟨0, _⟩ => .atom 0 [.rel [.iota], .iota]
    | ⟨1, _⟩ => .atom 2 [.rel [.iota], .iota]
  wires
    | ⟨0, _⟩ =>
        { sig := .rel [.rel [.iota], .iota]
          scope := 0
          endpoints := [⟨0, .head⟩, ⟨1, .head⟩] }
    | ⟨1, _⟩ =>
        { sig := .rel [.iota]
          scope := 0
          endpoints := [⟨0, .arg 0⟩] }
    | ⟨2, _⟩ =>
        { sig := .rel [.iota]
          scope := 0
          endpoints := [⟨1, .arg 0⟩] }
    | ⟨3, _⟩ =>
        { sig := .iota
          scope := 0
          endpoints := [⟨0, .arg 1⟩] }
    | ⟨4, _⟩ =>
        { sig := .iota
          scope := 0
          endpoints := [⟨1, .arg 1⟩] }

private theorem formalRaw_wellFormed : formalRaw.WellFormed [] := by
  native_decide

private def formal : CheckedDiagram [] :=
  ⟨formalRaw, formalRaw_wellFormed⟩

example :
    leafError? (applyApplyFormal formal (idx 0) 0 .backward) = none := by
  native_decide

example :
    leafError? (applyApplyFormal formal (idx 0) 0 .forward) =
      some .leafRequiresNegative := by
  native_decide

private def formalLeaf :=
  (applyApplyFormal formal (idx 0) 0 .backward).toOption.get
    (by native_decide)

example :
    (formalLeaf.target.val.nodes (idx 0),
      formalLeaf.target.val.nodes (idx 1)) =
      (.atom (idx 0) [.iota], .atom (idx 2) [.iota]) := by
  native_decide

example :
    leafError?
      (applyAbstractFormal formalLeaf.target [idx 0, idx 1] (idx 0)
        .forward) = none := by
  native_decide

private def formalAbstract :=
  (applyAbstractFormal formalLeaf.target formalLeaf.inverseNodes
      formalLeaf.inverseScope .forward).toOption.get (by native_decide)

private def formalTargetIdentityIso :
    ConcreteIso formalLeaf.target.val formalLeaf.target.val :=
  (ConcreteIso.checkEquivs? formalLeaf.target.val formalLeaf.target.val
      (Data.Finite.FiniteEquiv.refl _)
      (Data.Finite.FiniteEquiv.refl _)
      (Data.Finite.FiniteEquiv.refl _)).get (by native_decide)

example :
    (formalLeaf.inverseTransport formalAbstract
      formalTargetIdentityIso).isOk = true := by
  native_decide

example :
    leafError?
      (applyAbstractFormal formalLeaf.target [] (idx 0) .forward) =
      some (.concreteRejected .emptySelection) := by
  native_decide

example :
    leafError? (applyApplyFormal formal (idx 0) 1 .backward) =
      some (.concreteRejected .formalSignature) := by
  native_decide

example :
    leafError? (applyApplyFormal formal (idx 0) 2 .backward) =
      some (.concreteRejected .invalidPosition) := by
  native_decide

example :
    leafError? (applyApplyFormal formal (idx 3) 0 .backward) =
      some (.concreteRejected .expectedRelation) := by
  native_decide

example :
    leafError?
      (applyAbstractFormal formalLeaf.target [idx 0] (idx 2)
        .forward) =
      some (.concreteRejected .scopeDoesNotEnclose) := by
  native_decide

/-! A negative acted scope exercises the opposite two orientation gates. -/
private def negativeFormalRaw : ConcreteDiagram 0 where
  regionCount := 3
  nodeCount := 2
  wireCount := 5
  root := 0
  regions
    | ⟨0, _⟩ => .sheet
    | ⟨1, _⟩ => .cut 0
    | ⟨2, _⟩ => .cut 1
  nodes
    | ⟨0, _⟩ => .atom 1 [.rel [.iota], .iota]
    | ⟨1, _⟩ => .atom 2 [.rel [.iota], .iota]
  wires
    | ⟨0, _⟩ =>
        { sig := .rel [.rel [.iota], .iota]
          scope := 1
          endpoints := [⟨0, .head⟩, ⟨1, .head⟩] }
    | ⟨1, _⟩ =>
        { sig := .rel [.iota]
          scope := 1
          endpoints := [⟨0, .arg 0⟩] }
    | ⟨2, _⟩ =>
        { sig := .rel [.iota]
          scope := 1
          endpoints := [⟨1, .arg 0⟩] }
    | ⟨3, _⟩ =>
        { sig := .iota
          scope := 1
          endpoints := [⟨0, .arg 1⟩] }
    | ⟨4, _⟩ =>
        { sig := .iota
          scope := 1
          endpoints := [⟨1, .arg 1⟩] }

private theorem negativeFormalRaw_wellFormed :
    negativeFormalRaw.WellFormed [] := by
  native_decide

private def negativeFormal : CheckedDiagram [] :=
  ⟨negativeFormalRaw, negativeFormalRaw_wellFormed⟩

private def negativeFormalLeaf :=
  (applyApplyFormal negativeFormal (idx 0) 0 .forward).toOption.get
    (by native_decide)

example :
    leafError?
      (applyAbstractFormal negativeFormalLeaf.target [idx 0, idx 1]
        (idx 1) .backward) = none := by
  native_decide

/-! Identity leaves require at least two equal-signature arguments. -/
private def identityRaw : ConcreteDiagram 0 where
  regionCount := 1
  nodeCount := 2
  wireCount := 3
  root := 0
  regions := fun _ => .sheet
  nodes := fun _ => .atom 0 [.iota, .iota]
  wires
    | ⟨0, _⟩ =>
        { sig := .rel [.iota, .iota]
          scope := 0
          endpoints := [⟨0, .head⟩, ⟨1, .head⟩] }
    | ⟨1, _⟩ =>
        { sig := .iota
          scope := 0
          endpoints := [⟨0, .arg 0⟩, ⟨1, .arg 0⟩] }
    | ⟨2, _⟩ =>
        { sig := .iota
          scope := 0
          endpoints := [⟨0, .arg 1⟩, ⟨1, .arg 1⟩] }

private theorem identityRaw_wellFormed : identityRaw.WellFormed [] := by
  native_decide

private def identity : CheckedDiagram [] :=
  ⟨identityRaw, identityRaw_wellFormed⟩

private def identityLeaf :=
  (applyIdentityLeaf identity (idx 0) .backward).toOption.get
    (by native_decide)

example :
    (identityLeaf.target.val.nodes (idx 0),
      identityLeaf.target.val.nodes (idx 1)) =
      (.identity (idx 0) .iota 2, .identity (idx 0) .iota 2) := by
  native_decide

example :
    leafError?
      (applyIdentityAbstract identityLeaf.target [idx 0, idx 1] (idx 0)
        .forward) = none := by
  native_decide

private def identityAbstract :=
  (applyIdentityAbstract identityLeaf.target identityLeaf.inverseNodes
      identityLeaf.inverseScope .forward).toOption.get (by native_decide)

private def identityTargetIdentityIso :
    ConcreteIso identityLeaf.target.val identityLeaf.target.val :=
  (ConcreteIso.checkEquivs? identityLeaf.target.val identityLeaf.target.val
      (Data.Finite.FiniteEquiv.refl _)
      (Data.Finite.FiniteEquiv.refl _)
      (Data.Finite.FiniteEquiv.refl _)).get (by native_decide)

example :
    (identityLeaf.inverseTransport identityAbstract
      identityTargetIdentityIso).isOk = true := by
  native_decide

example :
    leafError?
      (applyIdentityAbstract identityLeaf.target [idx 0, idx 0] (idx 0)
        .forward) =
      some (.concreteRejected .duplicateSelection) := by
  native_decide

example :
    leafError? (applyIdentityLeaf formal (idx 0) .backward) =
      some (.concreteRejected .identitySignature) := by
  native_decide

/-!
Reference leaves use the chronological definition signature and remain one
folded `.ref`; no definition body is expanded into the concrete diagram.
-/
private def refRaw : ConcreteDiagram 1 where
  regionCount := 1
  nodeCount := 2
  wireCount := 3
  root := 0
  regions := fun _ => .sheet
  nodes := fun _ => .atom 0 [.iota]
  wires
    | ⟨0, _⟩ =>
        { sig := .rel [.iota]
          scope := 0
          endpoints := [⟨0, .head⟩, ⟨1, .head⟩] }
    | ⟨1, _⟩ =>
        { sig := .iota
          scope := 0
          endpoints := [⟨0, .arg 0⟩] }
    | ⟨2, _⟩ =>
        { sig := .iota
          scope := 0
          endpoints := [⟨1, .arg 0⟩] }

private theorem refRaw_wellFormed : refRaw.WellFormed [[.iota]] := by
  native_decide

private def refs : CheckedDiagram [[.iota]] :=
  ⟨refRaw, refRaw_wellFormed⟩

example :
    leafError? (applyIdentityLeaf refs (idx 0) .backward) =
      some (.concreteRejected .identityArity) := by
  native_decide

private def refLeaf :=
  (applyRefLeaf refs (idx 0) (idx 0) .backward).toOption.get
    (by native_decide)

example :
    (refLeaf.target.val.nodes (idx 0),
      refLeaf.target.val.nodes (idx 1)) =
      (.ref (idx 0) (idx 0) [.iota],
        .ref (idx 0) (idx 0) [.iota]) := by
  native_decide

example :
    leafError?
      (applyRefAbstract refLeaf.target [idx 0, idx 1] (idx 0)
        .forward) = none := by
  native_decide

private def refAbstract :=
  (applyRefAbstract refLeaf.target refLeaf.inverseNodes
      refLeaf.inverseScope .forward).toOption.get (by native_decide)

private def refTargetIdentityIso :
    ConcreteIso refLeaf.target.val refLeaf.target.val :=
  (ConcreteIso.checkEquivs? refLeaf.target.val refLeaf.target.val
      (Data.Finite.FiniteEquiv.refl _)
      (Data.Finite.FiniteEquiv.refl _)
      (Data.Finite.FiniteEquiv.refl _)).get (by native_decide)

example :
    (refLeaf.inverseTransport refAbstract
      refTargetIdentityIso).isOk = true := by
  native_decide

example :
    leafError?
      (applyRefAbstract identityLeaf.target [idx 0] (idx 0) .forward) =
      some (.concreteRejected .wrongNodeKind) := by
  native_decide

#check applyApplyFormal
#check applyAbstractFormal
#check applyIdentityLeaf
#check applyIdentityAbstract
#check applyRefLeaf
#check applyRefAbstract

#check apply_formal_sound
#check abstract_formal_sound
#check identity_leaf_sound
#check identity_abstract_sound
#check ref_leaf_sound
#check ref_abstract_sound

/-!
The generic topology primitives remain sound for arbitrary `PreModel`, while
each relation-synthesizing leaf theorem exposes the stronger `Model`
assumption in its public signature.
-/
#check wire_sever_sound
#check wire_join_sound
#check apply_formal_sound
#check identity_leaf_sound
#check ref_leaf_sound

end LeavesFixtures

end WirePrimitive

end VisualProof
