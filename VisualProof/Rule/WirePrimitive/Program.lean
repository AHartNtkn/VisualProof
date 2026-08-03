import VisualProof.Rule.Orientation
import VisualProof.Rule.Structural
import VisualProof.Rule.Vacuous
import VisualProof.Rule.WirePrimitive.VacuityTransport
import VisualProof.Rule.WirePrimitive.Partition
import VisualProof.Rule.WirePrimitive.Content
import VisualProof.Rule.WirePrimitive.Arguments
import VisualProof.Rule.WirePrimitive.Leaves

namespace VisualProof

namespace WirePrimitive

open Leaves
open StructuralCore

/-!
# Checked primitive programs

The content compiler never emits unchecked syntax.  Every node below owns the
opaque receipt returned by the corresponding primitive checker, and its target
index is definitionally the source index of the following node.  This is the
ordered execution and allocation receipt: intermediate diagrams, including
their freshly allocated finite identifiers, cannot be skipped or substituted.
-/

/--
The exact checked primitive subset available to the structural content
compiler.  `orientation` is common to the entire compiled action.
-/
inductive CompiledPrimitiveStep
    (orientation : Orientation) :
    CheckedDiagram definitions → Type
  | wireSever
      {source : CheckedDiagram definitions}
      (input : WireSeverInput source)
      (orientationExact : input.orientation = orientation)
      (applied : AppliedWireSever source input) :
      CompiledPrimitiveStep orientation source
  | wireJoin
      {source : CheckedDiagram definitions}
      (input : WireJoinInput source)
      (orientationExact : input.orientation = orientation)
      (applied : AppliedWireJoin source input) :
      CompiledPrimitiveStep orientation source
  | identityInsert
      {source : CheckedDiagram definitions}
      {fragment : CheckedOpenDiagram definitions}
      (input : StructuralCore.StructuralInsertionInput source fragment)
      (orientationExact : input.orientation = orientation)
      (checked : StructuralCore.StructuralInsertionReceipt input)
      (tagExact : checked.tag = .identityInsert) :
      CompiledPrimitiveStep orientation source
  | erasure
      {source : CheckedDiagram definitions}
      {base : CheckedDiagram definitions}
      {fragment : CheckedOpenDiagram definitions}
      (input : StructuralCore.StructuralErasureInput base fragment)
      (orientationExact : input.orientation = orientation)
      (checked : StructuralCore.StructuralErasureReceipt input)
      (sourceIso : ConcreteIso source.val checked.source.val)
      (tagExact : checked.insertedTag = .identityInsert) :
      CompiledPrimitiveStep orientation source
  | cutWrap
      {source : CheckedDiagram definitions}
      (wire : source.val.WireId)
      (applied : AppliedCutWrap source wire) :
      CompiledPrimitiveStep orientation source
  | cutAbsorb
      {source : CheckedDiagram definitions}
      (wire : source.val.WireId)
      (applied : AppliedCutAbsorb source wire) :
      CompiledPrimitiveStep orientation source
  | parallelSplit
      {source : CheckedDiagram definitions}
      (wire : source.val.WireId)
      (applied : AppliedParallelSplit source wire) :
      CompiledPrimitiveStep orientation source
  | parallelFuse
      {source : CheckedDiagram definitions}
      (left right : source.val.WireId)
      (applied : AppliedParallelFuse source left right) :
      CompiledPrimitiveStep orientation source
  | endsDelete
      {source : CheckedDiagram definitions}
      (wire : source.val.WireId)
      (applied : AppliedEndsDelete source orientation wire) :
      CompiledPrimitiveStep orientation source
  | endsSpawn
      {source : CheckedDiagram definitions}
      (wire : source.val.WireId)
      (sites : List (ConcreteWirePrimitive.EndSite source wire))
      (applied : AppliedEndsSpawn source orientation wire sites) :
      CompiledPrimitiveStep orientation source
  | vacuousElim
      {plain bound : CheckedDiagram definitions}
      (input : VacuousInput plain bound)
      (checked : CheckedVacuous input)
      (deletion : Vacuity.EliminationReceipt input checked) :
      CompiledPrimitiveStep orientation bound
  | vacuousIntro
      {plain bound : CheckedDiagram definitions}
      (input : VacuousInput plain bound)
      (checked : CheckedVacuous input)
      (deletion : Vacuity.EliminationReceipt input checked) :
      CompiledPrimitiveStep orientation plain
  | arityShift
      {source : CheckedDiagram definitions}
      (wire : source.val.WireId)
      (newArgument : Sig)
      (applied : AppliedArityShift source wire newArgument) :
      CompiledPrimitiveStep orientation source
  | arityUnshift
      {source : CheckedDiagram definitions}
      (wire : source.val.WireId)
      (position : Nat)
      (applied : AppliedArityUnshift source wire position) :
      CompiledPrimitiveStep orientation source
  | argPermute
      {source : CheckedDiagram definitions}
      (wire : source.val.WireId)
      (permutation : List Nat)
      (applied : AppliedArgPermute source wire permutation) :
      CompiledPrimitiveStep orientation source
  | argDuplicate
      {source : CheckedDiagram definitions}
      (wire : source.val.WireId)
      (position : Nat)
      (applied : AppliedArgDuplicate source wire position) :
      CompiledPrimitiveStep orientation source
  | argContract
      {source : CheckedDiagram definitions}
      (wire : source.val.WireId)
      (position : Nat)
      (applied : AppliedArgContract source wire position) :
      CompiledPrimitiveStep orientation source
  | argDrop
      {source : CheckedDiagram definitions}
      (wire : source.val.WireId)
      (position : Nat)
      (applied : AppliedArgDrop source orientation wire position) :
      CompiledPrimitiveStep orientation source
  | argExtend
      {source : CheckedDiagram definitions}
      (wire : source.val.WireId)
      (position : Nat)
      (newArgument : Sig)
      (attachments : List source.val.WireId)
      (applied :
        AppliedArgExtend source orientation wire position newArgument
          attachments) :
      CompiledPrimitiveStep orientation source
  | applyFormal
      {source : CheckedDiagram definitions}
      (wire : source.val.WireId)
      (position : Nat)
      (applied :
        AppliedApplyFormal source orientation wire position) :
      CompiledPrimitiveStep orientation source
  | abstractFormal
      {source : CheckedDiagram definitions}
      (nodes : List source.val.NodeId)
      (scope : source.val.RegionId)
      (applied :
        AppliedAbstractFormal source orientation nodes scope) :
      CompiledPrimitiveStep orientation source
  | identityLeaf
      {source : CheckedDiagram definitions}
      (wire : source.val.WireId)
      (applied : AppliedIdentityLeaf source orientation wire) :
      CompiledPrimitiveStep orientation source
  | identityAbstract
      {source : CheckedDiagram definitions}
      (nodes : List source.val.NodeId)
      (scope : source.val.RegionId)
      (applied :
        AppliedIdentityAbstract source orientation nodes scope) :
      CompiledPrimitiveStep orientation source
  | refLeaf
      {source : CheckedDiagram definitions}
      (wire : source.val.WireId)
      (definition : Fin definitions.length)
      (applied :
        AppliedRefLeaf source orientation wire definition) :
      CompiledPrimitiveStep orientation source
  | refAbstract
      {source : CheckedDiagram definitions}
      (nodes : List source.val.NodeId)
      (scope : source.val.RegionId)
      (applied :
        AppliedRefAbstract source orientation nodes scope) :
      CompiledPrimitiveStep orientation source

namespace CompiledPrimitiveStep

/-- The checked result allocated by one primitive receipt. -/
def target :
    {source : CheckedDiagram definitions} →
      CompiledPrimitiveStep orientation source →
        CheckedDiagram definitions
  | _, .wireSever _ _ applied => applied.target
  | _, .wireJoin _ _ applied => applied.target
  | _, .identityInsert _ _ checked _ => checked.target
  | _, .erasure _ _ checked _ _ => checked.target
  | _, .cutWrap _ applied => applied.target
  | _, .cutAbsorb _ applied => applied.target
  | _, .parallelSplit _ applied => applied.target
  | _, .parallelFuse _ _ applied => applied.target
  | _, .endsDelete _ applied => applied.target
  | _, .endsSpawn _ _ applied => applied.target
  | _, .vacuousElim _ checked _ => checked.plain
  | _, .vacuousIntro _ checked _ => checked.bound
  | _, .arityShift _ _ applied => applied.target
  | _, .arityUnshift _ _ applied => applied.target
  | _, .argPermute _ _ applied => applied.target
  | _, .argDuplicate _ _ applied => applied.target
  | _, .argContract _ _ applied => applied.target
  | _, .argDrop _ _ applied => applied.target
  | _, .argExtend _ _ _ _ applied => applied.target
  | _, .applyFormal _ _ applied => applied.target
  | _, .abstractFormal _ _ applied => applied.target
  | _, .identityLeaf _ applied => applied.target
  | _, .identityAbstract _ _ applied => applied.target
  | _, .refLeaf _ _ applied => applied.target
  | _, .refAbstract _ _ applied => applied.target

/-- Stable public tag for one compiled primitive receipt. -/
def tag :
    {source : CheckedDiagram definitions} →
      CompiledPrimitiveStep orientation source → StepTag
  | _, .wireSever .. => .wireSever
  | _, .wireJoin .. => .wireJoin
  | _, .identityInsert .. => .identityInsert
  | _, .erasure .. => .erasure
  | _, .cutWrap .. => .cutWrap
  | _, .cutAbsorb .. => .cutAbsorb
  | _, .parallelSplit .. => .parallelSplit
  | _, .parallelFuse .. => .parallelFuse
  | _, .endsDelete .. => .endsDelete
  | _, .endsSpawn .. => .endsSpawn
  | _, .vacuousElim .. => .vacuousElim
  | _, .vacuousIntro .. => .vacuousIntro
  | _, .arityShift .. => .arityShift
  | _, .arityUnshift .. => .arityUnshift
  | _, .argPermute .. => .argPermute
  | _, .argDuplicate .. => .argDuplicate
  | _, .argContract .. => .argContract
  | _, .argDrop .. => .argDrop
  | _, .argExtend .. => .argExtend
  | _, .applyFormal .. => .applyFormal
  | _, .abstractFormal .. => .abstractFormal
  | _, .identityLeaf .. => .identityLeaf
  | _, .identityAbstract .. => .identityAbstract
  | _, .refLeaf .. => .refLeaf
  | _, .refAbstract .. => .refAbstract

end CompiledPrimitiveStep

/--
An ordered, dependently typed primitive trace.  The target allocated by each
head receipt is definitionally the source of its tail.
-/
inductive PrimitiveProgram
    (orientation : Orientation) :
    CheckedDiagram definitions → Type
  | nil (source : CheckedDiagram definitions) :
      PrimitiveProgram orientation source
  | cons
      {source : CheckedDiagram definitions}
      (head : CompiledPrimitiveStep orientation source)
      (tail : PrimitiveProgram orientation head.target) :
      PrimitiveProgram orientation source

namespace PrimitiveProgram

/-- Final checked diagram produced by replaying the complete receipt chain. -/
def target :
    {source : CheckedDiagram definitions} →
      PrimitiveProgram orientation source →
        CheckedDiagram definitions
  | source, .nil _ => source
  | _, .cons _ tail => tail.target

/-- A primitive receipt chain together with its construction-owned landing.
The planned diagram is explicit, so structural compilers can compose landing
correspondences instead of rediscovering the final graph. -/
structure ConstructionLanding
    (orientation : Orientation)
    (source planned : CheckedDiagram definitions) where
  program : PrimitiveProgram orientation source
  constructionIso : ConcreteIso program.target.val planned.val

namespace ConstructionLanding

/-- Exact landing of an already constructed primitive program. -/
def exact
    (program : PrimitiveProgram orientation source) :
    ConstructionLanding orientation source program.target where
  program := program
  constructionIso := Vacuity.identityIso program.target.val
    program.target.property

/-- Retarget a construction landing by composing an owned correspondence. -/
def retarget
    (landing : ConstructionLanding orientation source middle)
    (next : ConcreteIso middle.val planned.val) :
    ConstructionLanding orientation source planned where
  program := landing.program
  constructionIso := landing.constructionIso.trans next

end ConstructionLanding

/-- Exact ordered public tag trace. -/
def tags :
    {source : CheckedDiagram definitions} →
      PrimitiveProgram orientation source → List StepTag
  | _, .nil _ => []
  | _, .cons head tail => head.tag :: tail.tags

/-- Number of checked primitive transitions in the program. -/
def length :
    {source : CheckedDiagram definitions} →
      PrimitiveProgram orientation source → Nat
  | _, .nil _ => 0
  | _, .cons _ tail => tail.length + 1

/-- Append two programs whose dependent boundary is exact. -/
def append :
    {source : CheckedDiagram definitions} →
      (first : PrimitiveProgram orientation source) →
      PrimitiveProgram orientation first.target →
      PrimitiveProgram orientation source
  | _, .nil _, second => second
  | _, .cons head tail, second =>
      .cons head (tail.append second)

@[simp]
theorem target_append
    {source : CheckedDiagram definitions}
    (first : PrimitiveProgram orientation source)
    (second : PrimitiveProgram orientation first.target) :
    (first.append second).target = second.target := by
  induction first with
  | nil => rfl
  | cons head tail induction =>
      exact induction second

end PrimitiveProgram

/--
Replay is total because a `PrimitiveProgram` already is the complete checked
execution receipt.  The result includes every intermediate allocation through
the dependent indices retained by the program.
-/
def runPrimitiveProgram
    {source : CheckedDiagram definitions}
    (program : PrimitiveProgram orientation source) :
    CheckedDiagram definitions :=
  program.target

end WirePrimitive

end VisualProof
