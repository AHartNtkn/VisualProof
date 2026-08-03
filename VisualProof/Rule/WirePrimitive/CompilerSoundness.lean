import VisualProof.Rule.WirePrimitive.Compiler
import VisualProof.Diagram.Concrete.ElaborationInvariance

namespace VisualProof

universe u

namespace WirePrimitive

namespace CompiledPrimitiveStep

private theorem equivalenceDirected
    (orientation : Orientation)
    {source target : Prop}
    (equivalence : source ↔ target) :
    Directed orientation source target := by
  cases orientation with
  | forward => exact equivalence.mp
  | backward => exact equivalence.mpr

/-- Every checked primitive emitted by the compiler has its public semantics. -/
theorem sound
    {source : CheckedDiagram definitions}
    (step : CompiledPrimitiveStep orientation source)
    (model : Model.{u})
    (definitionEnv : DefinitionEnv model.toPreModel definitions) :
    Directed orientation
      (denoteChecked model.toPreModel definitionEnv source)
      (denoteChecked model.toPreModel definitionEnv step.target) := by
  cases step with
  | wireSever input orientationExact applied =>
      subst orientationExact
      exact wire_sever_sound input applied model.toPreModel definitionEnv
  | wireJoin input orientationExact applied =>
      subst orientationExact
      exact wire_join_sound input applied model.toPreModel definitionEnv
  | identityInsert input orientationExact checked _ =>
      subst orientationExact
      exact checked.sound model.toPreModel definitionEnv
  | erasure input orientationExact checked _ =>
      change Directed orientation
        (denoteChecked model.toPreModel definitionEnv checked.source)
        (denoteChecked model.toPreModel definitionEnv checked.target)
      rw [← orientationExact]
      exact checked.sound model.toPreModel definitionEnv
  | cutWrap wire applied =>
      exact equivalenceDirected orientation <|
        cut_wrap_sound wire applied model definitionEnv
  | cutAbsorb wire applied =>
      exact equivalenceDirected orientation <|
        cut_absorb_sound wire applied model definitionEnv
  | parallelSplit wire applied =>
      exact equivalenceDirected orientation <|
        parallel_split_sound wire applied model definitionEnv
  | parallelFuse left right applied =>
      exact equivalenceDirected orientation <|
        parallel_fuse_sound left right applied model definitionEnv
  | endsDelete wire applied =>
      exact ends_delete_sound orientation wire applied model definitionEnv
  | endsSpawn wire sites applied =>
      exact
        ends_spawn_sound orientation wire sites applied model definitionEnv
  | vacuousElim input checked _ =>
      exact equivalenceDirected orientation <|
        checked.equivalence model.toPreModel definitionEnv
  | vacuousIntro input checked _ =>
      exact equivalenceDirected orientation <|
        (checked.equivalence model.toPreModel definitionEnv).symm
  | arityShift wire newArgument applied =>
      exact equivalenceDirected orientation <|
        arity_shift_sound wire newArgument applied model definitionEnv
  | arityUnshift wire position applied =>
      exact equivalenceDirected orientation <|
        arity_unshift_sound wire position applied model definitionEnv
  | argPermute wire permutation applied =>
      exact equivalenceDirected orientation <|
        arg_permute_sound wire permutation applied model definitionEnv
  | argDuplicate wire position applied =>
      exact equivalenceDirected orientation <|
        arg_duplicate_sound wire position applied model definitionEnv
  | argContract wire position applied =>
      exact equivalenceDirected orientation <|
        arg_contract_sound wire position applied model definitionEnv
  | argDrop wire position applied =>
      exact
        arg_drop_sound wire position orientation applied model definitionEnv
  | argExtend wire position newArgument attachments applied =>
      exact
        arg_extend_sound wire position newArgument attachments orientation
          applied model definitionEnv
  | applyFormal wire position applied =>
      exact
        Leaves.apply_formal_sound wire position orientation applied model
          definitionEnv
  | abstractFormal nodes scope applied =>
      exact
        Leaves.abstract_formal_sound nodes scope orientation applied model
          definitionEnv
  | identityLeaf wire applied =>
      exact
        Leaves.identity_leaf_sound wire orientation applied model definitionEnv
  | identityAbstract nodes scope applied =>
      exact
        Leaves.identity_abstract_sound nodes scope orientation applied model
          definitionEnv
  | refLeaf wire definition applied =>
      exact
        Leaves.ref_leaf_sound wire definition orientation applied model
          definitionEnv
  | refAbstract nodes scope applied =>
      exact
        Leaves.ref_abstract_sound nodes scope orientation applied model
          definitionEnv

end CompiledPrimitiveStep

/--
Semantic composition follows the exact dependent execution chain; no
intermediate boundary or allocation can be replaced.
-/
theorem runPrimitiveProgram_sound
    {source : CheckedDiagram definitions}
    (program : PrimitiveProgram orientation source)
    (model : Model.{u})
    (definitionEnv : DefinitionEnv model.toPreModel definitions) :
    Directed orientation
      (denoteChecked model.toPreModel definitionEnv source)
      (denoteChecked model.toPreModel definitionEnv
        (runPrimitiveProgram program)) := by
  induction program with
  | nil =>
      cases orientation <;> exact id
  | cons head tail induction =>
      have headSound := head.sound model definitionEnv
      have tailSound := induction
      cases orientation with
      | forward =>
          exact fun sourceHolds => tailSound (headSound sourceHolds)
      | backward =>
          exact fun targetHolds => headSound (tailSound targetHolds)

/-- Exact raw-construction redundancy certificate for a compiled strongest
join. -/
theorem compiled_join_redundant
    {source : CheckedDiagram definitions}
    {input : MonolithicRelationJoinInput source}
    (compiled : CompiledRelationJoin input) :
    Nonempty
      (ConcreteIso compiled.program.target.val
        compiled.monolithic.plainFinal.val) :=
  ⟨compiled.constructionIso⟩

/-- Exact checked redundancy certificate for a compiled strongest sever. -/
theorem compiled_sever_redundant
    {source : CheckedDiagram definitions}
    {input : MonolithicRelationSeverInput source}
    (compiled : CompiledRelationSever input) :
    Nonempty
      (ConcreteIso compiled.program.target.val
        compiled.monolithic.target.val) :=
  ⟨compiled.constructionIso⟩

/--
The raw monolithic join direction follows from the primitive program and the
independently checked construction isomorphism.
-/
theorem compiled_join_sound
    {source : CheckedDiagram definitions}
    {input : MonolithicRelationJoinInput source}
    (compiled : CompiledRelationJoin input)
    (model : Model.{u})
    (definitionEnv : DefinitionEnv model.toPreModel definitions) :
    Directed input.orientation
      (denoteChecked model.toPreModel definitionEnv source)
      (denoteChecked model.toPreModel definitionEnv
        compiled.monolithic.plainFinal) := by
  have programSound :=
    runPrimitiveProgram_sound compiled.program model definitionEnv
  have targetEquivalent :=
    iso_denotation compiled.constructionIso model.toPreModel definitionEnv
  cases orientationExact : input.orientation with
  | forward =>
      have primitiveDirection :
          denoteChecked model.toPreModel definitionEnv source →
            denoteChecked model.toPreModel definitionEnv
              compiled.program.target := by
        simpa [orientationExact] using programSound
      exact fun sourceHolds =>
        targetEquivalent.mp (primitiveDirection sourceHolds)
  | backward =>
      have primitiveDirection :
          denoteChecked model.toPreModel definitionEnv
              compiled.program.target →
            denoteChecked model.toPreModel definitionEnv source := by
        simpa [orientationExact] using programSound
      exact fun targetHolds =>
        primitiveDirection (targetEquivalent.mpr targetHolds)

/--
The monolithic sever direction follows again from the reversed primitive
program and the independently checked final isomorphism.
-/
theorem compiled_sever_sound
    {source : CheckedDiagram definitions}
    {input : MonolithicRelationSeverInput source}
    (compiled : CompiledRelationSever input)
    (model : Model.{u})
    (definitionEnv : DefinitionEnv model.toPreModel definitions) :
    Directed input.orientation
      (denoteChecked model.toPreModel definitionEnv source)
      (denoteChecked model.toPreModel definitionEnv
        compiled.monolithic.target) := by
  have programSound :=
    runPrimitiveProgram_sound compiled.program model definitionEnv
  have targetEquivalent :=
    iso_denotation compiled.constructionIso model.toPreModel definitionEnv
  cases orientationExact : input.orientation with
  | forward =>
      have primitiveDirection :
          denoteChecked model.toPreModel definitionEnv source →
            denoteChecked model.toPreModel definitionEnv
              compiled.program.target := by
        simpa [orientationExact] using programSound
      exact fun sourceHolds =>
        targetEquivalent.mp (primitiveDirection sourceHolds)
  | backward =>
      have primitiveDirection :
          denoteChecked model.toPreModel definitionEnv
              compiled.program.target →
            denoteChecked model.toPreModel definitionEnv source := by
        simpa [orientationExact] using programSound
      exact fun targetHolds =>
        primitiveDirection (targetEquivalent.mpr targetHolds)

end WirePrimitive

end VisualProof
