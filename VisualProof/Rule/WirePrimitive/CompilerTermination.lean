import VisualProof.Rule.WirePrimitive.Program

namespace VisualProof

namespace WirePrimitive

/-!
# Proof-carrying intrinsic compiler residual

`OpenCompilation.body` is the checked, intrinsically typed content syntax.
The total compiler recurses over that syntax rather than reconstructing a
possibly-invalid concrete slice.  The older concrete `ContentResidual` below
remains temporarily as the executable comparison path while the compiler is
migrated; it is not sufficient evidence for totality by itself.
-/

/-- The signature carried by one existentially packed intrinsic variable. -/
def packedVarSignature (value : PackedVar context) : Sig := value.1

/-- Weaken one packed variable below a newly introduced binder. -/
def liftPackedVar (value : PackedVar context) : PackedVar (bound :: context) :=
  ⟨value.1, .there value.2⟩

/-- One content class whose current representative is an ambient host wire. -/
structure AmbientBinding
    (source : CheckedDiagram definitions)
    (context : List Sig)
    (live : source.val.WireId) where
  value : PackedVar context
  wire : source.val.WireId
  different : wire ≠ live
  signature : (source.val.wires wire).sig = value.1

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
  signature :=
    (applied.transportRetainedWire_signature
      binding.wire binding.different).trans binding.signature

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

end IntrinsicCompilerResidual

/-!
# Structural compiler residual and termination order

The content-side identifiers remain those of the one checked open diagram.
A slice records only the live subgraph selected by previous parallel/cut
decompositions.  Host identifiers are carried separately by the compiler's
dependent state and therefore cannot be confused with content identifiers.
-/

/-- The live content slice still owed by one host relation wire. -/
structure ContentResidual
    (content : CheckedOpenDiagram definitions) where
  compilation : OpenCompilation content
  root : content.val.diagram.RegionId
  regions : List content.val.diagram.RegionId
  nodes : List content.val.diagram.NodeId
  wires : List content.val.diagram.WireId
  boundary : List content.val.diagram.WireId
  formals : Nat

namespace ContentResidual

/-- Root-scoped binders not yet promoted to formal positions. -/
def internalRootWires
    (residual : ContentResidual content) :
    List content.val.diagram.WireId :=
  residual.wires.filter fun wire =>
    decide (
      (content.val.diagram.wires wire).scope = residual.root ∧
      wire ∉ residual.boundary)

/-- Direct active nodes at the residual root. -/
def rootNodes
    (residual : ContentResidual content) :
    List content.val.diagram.NodeId :=
  residual.nodes.filter fun node =>
    decide ((content.val.diagram.nodes node).region = residual.root)

/-- Direct active cut children at the residual root. -/
def rootCuts
    (residual : ContentResidual content) :
    List content.val.diagram.RegionId :=
  residual.regions.filter fun region =>
    match content.val.diagram.regions region with
    | .sheet => false
    | .cut parent => decide (parent = residual.root)

/--
Primary structural component: active nodes, active regions, and precisely the
internal (not boundary) wires.  Promoting a root binder therefore decreases
this component even though the graph itself is unchanged.
-/
def structuralSize
    (residual : ContentResidual content) : Nat :=
  residual.nodes.length +
    (residual.wires.filter fun wire =>
      decide (wire ∉ residual.boundary)).length +
    residual.regions.length

/--
Secondary component used only while arranging a leaf's exact ordered
argument tuple.
-/
def plumbingSize
    (residual : ContentResidual content) : Nat :=
  residual.boundary.length + residual.formals

/-- The plan-mandated lexicographic termination measure. -/
def measure
    (residual : ContentResidual content) : Nat × Nat :=
  (residual.structuralSize, residual.plumbingSize)

/-- Exact lexicographic order used by the structural compiler. -/
abbrev Before :
    (Nat × Nat) → (Nat × Nat) → Prop :=
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

theorem before_of_structural
    {next current : ContentResidual content}
    (smaller : next.structuralSize < current.structuralSize) :
    Before next.measure current.measure :=
  Prod.Lex.left _ _ smaller

theorem before_of_plumbing
    {next current : ContentResidual content}
    (same :
      next.structuralSize = current.structuralSize)
    (smaller : next.plumbingSize < current.plumbingSize) :
    Before next.measure current.measure := by
  rw [measure, measure, same]
  exact Prod.Lex.right _ smaller

end ContentResidual

/--
One live host wire paired with its remaining content and chronological ambient
stub map.  The map is ordered rather than keyed so repeated boundary
positions remain visible.
-/
structure CompilerResidual
    (source : CheckedDiagram definitions)
    (content : CheckedOpenDiagram definitions) where
  wire : source.val.WireId
  contentState : ContentResidual content
  ambients :
    List (content.val.diagram.WireId × source.val.WireId)

/-- Compiler recursion is well founded solely by the content residual. -/
def compilerResidualMeasure
    (residual : CompilerResidual source content) : Nat × Nat :=
  residual.contentState.measure

end WirePrimitive

end VisualProof
