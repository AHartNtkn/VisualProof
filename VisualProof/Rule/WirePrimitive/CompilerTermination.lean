import VisualProof.Rule.WirePrimitive.Program

namespace VisualProof

namespace WirePrimitive

/-!
# Proof-carrying intrinsic compiler residual

`OpenCompilation.body` is the checked, intrinsically typed content syntax.
The total compiler recurses over that syntax rather than reconstructing a
possibly-invalid concrete slice.
-/

/-- The signature carried by one existentially packed intrinsic variable. -/
def packedVarSignature (value : PackedVar context) : Sig := value.1

/-- Weaken one packed variable below a newly introduced binder. -/
def liftPackedVar (value : PackedVar context) : PackedVar (bound :: context) :=
  ⟨value.1, .there value.2⟩

@[simp]
theorem varsEntries_signatures
    (values : Vars context signatures) :
    values.entries.map packedVarSignature = signatures := by
  induction values with
  | nil => rfl
  | cons head tail induction =>
      simp [Vars.entries, induction, packedVarSignature]

@[simp]
theorem varsEntries_length
    (values : Vars context signatures) :
    values.entries.length = signatures.length := by
  rw [← List.length_map, varsEntries_signatures]

/-- One content class whose current representative is an ambient host wire. -/
structure AmbientBinding
    (source : CheckedDiagram definitions)
    (context : List Sig)
    (live : source.val.WireId) where
  value : PackedVar context
  wire : source.val.WireId
  different : wire ≠ live

/--
The complete live obligation consumed by the total structural compiler.

`formals` is ordered and may repeat; `ambients` supplies representatives for
the remaining content classes.  `covers` rules out the missing-ambient
failure before execution, while `ambient_ne_live` rules out accidental
consumption when the live relation wire is replaced.
-/
structure IntrinsicCompilerResidual
    (source : CheckedDiagram definitions)
    (context : List Sig) where
  body : Region definitions context
  wire : source.val.WireId
  arguments : List Sig
  wire_signature : (source.val.wires wire).sig = .rel arguments
  sites : AllAppliedSites source wire
  formals : List (PackedVar context)
  formal_signatures : formals.map packedVarSignature = arguments
  ambients : List (AmbientBinding source context wire)
  covers :
    ∀ (signature : Sig) (value : Var context signature),
      (⟨signature, value⟩ : PackedVar context) ∈ formals ∨
        ∃ binding, binding ∈ ambients ∧
          binding.value = (⟨signature, value⟩ : PackedVar context)

namespace AmbientBinding

/-- Build the complete ordered ambient ledger from an intrinsic boundary
suffix and its equally ordered host parameters.  Repeated intrinsic classes
and repeated host wires remain separate entries. -/
def ofBoundaryLists
    {source : CheckedDiagram definitions}
    {live : source.val.WireId} :
    (values : List (PackedVar context)) →
    (wires : List source.val.WireId) →
    values.map packedVarSignature =
      wires.map (fun wire => (source.val.wires wire).sig) →
    live ∉ wires →
    List (AmbientBinding source context live)
  | [], [], _, _ => []
  | value :: values, wire :: wires, signatures, different => by
      have tailSignatures :
          values.map packedVarSignature =
            wires.map (fun candidate =>
              (source.val.wires candidate).sig) := by
        have tails := congrArg List.tail signatures
        simpa using tails
      have wireDifferent : wire ≠ live := by
        intro same
        apply different
        simp [same]
      have tailDifferent : live ∉ wires := by
        intro member
        exact different (List.mem_cons_of_mem wire member)
      exact
        { value := value
          wire := wire
          different := wireDifferent } ::
        ofBoundaryLists values wires tailSignatures tailDifferent
  | [], _ :: _, signatures, _ => by
      simp at signatures
  | _ :: _, [], signatures, _ => by
      simp at signatures

@[simp]
theorem ofBoundaryLists_values
    {source : CheckedDiagram definitions}
    {live : source.val.WireId}
    (values : List (PackedVar context))
    (wires : List source.val.WireId)
    (signatures :
      values.map packedVarSignature =
        wires.map (fun wire => (source.val.wires wire).sig))
    (different : live ∉ wires) :
    (ofBoundaryLists values wires signatures different).map
        AmbientBinding.value = values := by
  induction values generalizing wires with
  | nil =>
      cases wires with
      | nil => rfl
      | cons wire wires => simp at signatures
  | cons value values induction =>
      cases wires with
      | nil => simp at signatures
      | cons wire wires =>
          simp only [ofBoundaryLists, List.map_cons]
          congr
          apply induction

@[simp]
theorem ofBoundaryLists_wires
    {source : CheckedDiagram definitions}
    {live : source.val.WireId}
    (values : List (PackedVar context))
    (wires : List source.val.WireId)
    (signatures :
      values.map packedVarSignature =
        wires.map (fun wire => (source.val.wires wire).sig))
    (different : live ∉ wires) :
    (ofBoundaryLists values wires signatures different).map
        AmbientBinding.wire = wires := by
  induction values generalizing wires with
  | nil =>
      cases wires with
      | nil => rfl
      | cons wire wires => simp at signatures
  | cons value values induction =>
      cases wires with
      | nil => simp at signatures
      | cons wire wires =>
          simp only [ofBoundaryLists, List.map_cons]
          congr
          apply induction

/-- Transport one ambient class below a newly introduced formal binder. -/
def liftThroughArityShift
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {bound : Sig}
    (applied : AppliedArityShift source wire bound)
    (binding : AmbientBinding source context wire) :
    AmbientBinding applied.target (bound :: context) applied.targetWire where
  value := liftPackedVar binding.value
  wire := applied.transportRetainedWire binding.wire binding.different
  different :=
    applied.transportRetainedWire_ne_targetWire
      binding.wire binding.different

end AmbientBinding

mutual

/-- Number of remaining intrinsic constructors in one checked region. -/
def intrinsicRegionSize : Region definitions context → Nat
  | .mk items => intrinsicItemSeqSize items

/-- Number of remaining intrinsic constructors in one checked item. -/
def intrinsicItemSize : Item definitions context → Nat
  | .atom _ _ => 1
  | .named _ _ => 1
  | .identity _ _ _ => 1
  | .cut body => 1 + intrinsicRegionSize body
  | .bind _ body => 1 + intrinsicRegionSize body

/-- Number of remaining intrinsic constructors in an ordered conjunction. -/
def intrinsicItemSeqSize : ItemSeq definitions context → Nat
  | .nil => 0
  | .cons head tail =>
      intrinsicItemSize head + intrinsicItemSeqSize tail

end

namespace IntrinsicCompilerResidual

/--
Construct the first total compiler obligation from the sole checked open-body
compilation.  The ordered boundary is partitioned once: its prefix is the
possibly-repeated formal tuple and its suffix supplies one ambient binding per
ordered host parameter.  Boundary surjectivity proves that this partition
covers every intrinsic class.
-/
def initial
    {definitions : List (List Sig)}
    {content : CheckedOpenDiagram definitions}
    (compilation : OpenCompilation content)
    {source : CheckedDiagram definitions}
    (wire : source.val.WireId)
    (arguments : List Sig)
    (wireSignature : (source.val.wires wire).sig = .rel arguments)
    (sites : AllAppliedSites source wire)
    (parameters : List source.val.WireId)
    (formalSignatures :
      (checkedBoundarySigs content).take arguments.length = arguments)
    (parameterSignatures :
      (checkedBoundarySigs content).drop arguments.length =
        parameters.map (fun parameter =>
          (source.val.wires parameter).sig))
    (liveNotParameter : wire ∉ parameters) :
    IntrinsicCompilerResidual source
      (ConcreteElaboration.openBoundaryClassSigs content.val) := by
  let entries := compilation.boundary.entries
  let formals := entries.take arguments.length
  let ambientValues := entries.drop arguments.length
  have ambientSignatures :
      ambientValues.map packedVarSignature =
        parameters.map (fun parameter =>
          (source.val.wires parameter).sig) := by
    calc
      ambientValues.map packedVarSignature =
          (entries.map packedVarSignature).drop arguments.length := by
        simp [ambientValues, entries, List.map_drop]
      _ = (checkedBoundarySigs content).drop arguments.length := by
        rw [varsEntries_signatures]
      _ = parameters.map (fun parameter =>
          (source.val.wires parameter).sig) := parameterSignatures
  let ambients :=
    AmbientBinding.ofBoundaryLists ambientValues parameters
      ambientSignatures liveNotParameter
  exact
    { body := compilation.body
      wire := wire
      arguments := arguments
      wire_signature := wireSignature
      sites := sites
      formals := formals
      formal_signatures := by
        calc
          formals.map packedVarSignature =
              (entries.map packedVarSignature).take arguments.length := by
            simp [formals, entries, List.map_take]
          _ = (checkedBoundarySigs content).take arguments.length := by
            rw [varsEntries_signatures]
          _ = arguments := formalSignatures
      ambients := ambients
      covers := by
        intro signature value
        let packed : PackedVar
            (ConcreteElaboration.openBoundaryClassSigs content.val) :=
          ⟨signature, value⟩
        have member : packed ∈ entries := by
          exact compilation.openDiagram.boundary_surjective signature value
        have partitioned :
            packed ∈ formals ∨ packed ∈ ambientValues := by
          have combined : entries.take arguments.length ++
                entries.drop arguments.length = entries :=
            List.take_append_drop arguments.length entries
          have inCombined :
              packed ∈ entries.take arguments.length ++
                entries.drop arguments.length := by
            rw [combined]
            exact member
          simpa [formals, ambientValues] using
            (List.mem_append.mp inCombined)
        cases partitioned with
        | inl formal => exact Or.inl formal
        | inr ambient =>
            right
            have mapped :
                packed ∈ ambients.map AmbientBinding.value := by
              rw [AmbientBinding.ofBoundaryLists_values]
              exact ambient
            rcases List.mem_map.mp mapped with
              ⟨binding, bindingMember, bindingExact⟩
            exact ⟨binding, bindingMember, bindingExact⟩ }

/--
Advance the proof-carrying obligation below one intrinsic binder after its
checked arity shift.  Every former class is weakened, the new bound class is
the final formal argument, and every ambient host representative is carried
through the construction-owned retained-wire map.
-/
def enterBinder
    {definitions : List (List Sig)}
    {source : CheckedDiagram definitions}
    {context : List Sig}
    (residual : IntrinsicCompilerResidual source context)
    (bound : Sig)
    (body : Region definitions (bound :: context))
    (applied : AppliedArityShift source residual.wire bound) :
    IntrinsicCompilerResidual applied.target (bound :: context) where
  body := body
  wire := applied.targetWire
  arguments := applied.sourceArgumentList ++ [bound]
  wire_signature := applied.targetWire_signature
  sites := applied.targetSites
  formals := residual.formals.map liftPackedVar ++
    [⟨bound, .here⟩]
  formal_signatures := by
    have argumentsExact :
        residual.arguments = applied.sourceArgumentList :=
      Sig.rel.inj
        (residual.wire_signature.symm.trans
          applied.sourceWire_signature)
    calc
      (residual.formals.map
          (liftPackedVar (bound := bound)) ++
          [(⟨bound, (.here : Var (bound :: context) bound)⟩ :
            PackedVar (bound :: context))]).map packedVarSignature =
          residual.formals.map packedVarSignature ++ [bound] := by
        rw [List.map_append, List.map_map]
        have lifted :
            residual.formals.map
                (fun value => packedVarSignature
                  (liftPackedVar (bound := bound) value)) =
              residual.formals.map packedVarSignature := by
          apply List.map_congr_left
          intro value _member
          rcases value with ⟨signature, tailValue⟩
          rfl
        change
          residual.formals.map
              (fun value => packedVarSignature
                (liftPackedVar (bound := bound) value)) ++ [bound] =
            residual.formals.map packedVarSignature ++ [bound]
        rw [lifted]
      _ = residual.arguments ++ [bound] := by
        rw [residual.formal_signatures]
      _ = applied.sourceArgumentList ++ [bound] := by
        rw [argumentsExact]
  ambients := residual.ambients.map fun binding =>
    binding.liftThroughArityShift applied
  covers := by
    intro signature value
    cases value with
    | here =>
        left
        apply List.mem_append.mpr
        right
        simp [liftPackedVar]
    | there tail =>
        rcases residual.covers signature tail with
          formal | ⟨binding, member, exact⟩
        · left
          apply List.mem_append.mpr
          left
          apply List.mem_map.mpr
          exact ⟨⟨signature, tail⟩, formal, rfl⟩
        · right
          refine
            ⟨binding.liftThroughArityShift applied,
              List.mem_map.mpr ⟨binding, member, rfl⟩, ?_⟩
          exact congrArg liftPackedVar exact

/-- The plan-mandated structural/plumbing lexicographic measure. -/
def measure
    (residual : IntrinsicCompilerResidual source context) : Nat × Nat :=
  (intrinsicRegionSize residual.body,
    residual.formals.length + residual.ambients.length)

/-- The intrinsic structural component of the measure. -/
theorem measure_fst
    (residual : IntrinsicCompilerResidual source context) :
    residual.measure.1 = intrinsicRegionSize residual.body := rfl

/-- Exact lexicographic order for intrinsic structural compilation. -/
abbrev Before : (Nat × Nat) → (Nat × Nat) → Prop :=
  Prod.Lex Nat.lt Nat.lt

instance beforeDecidable (left right : Nat × Nat) :
    Decidable (Before left right) := by
  exact
    decidable_of_iff
      (left.1 < right.1 ∨
        left.1 = right.1 ∧ left.2 < right.2)
      Prod.lex_def.symm

theorem before_wellFounded : WellFounded Before :=
  (Prod.lex
    (inferInstance : WellFoundedRelation Nat)
    (inferInstance : WellFoundedRelation Nat)).wf

end IntrinsicCompilerResidual

end WirePrimitive

end VisualProof
