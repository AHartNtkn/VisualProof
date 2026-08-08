# Task 9 DoubleCut elimination interim report

Status: `BLOCKED_FOR_NEXT_SUBTASK`

## Completed GREEN boundary

The focused structural kernel for DoubleCut elimination is complete:

- `DoubleCutElimTransport.lean` owns the checked shape consequences, compact
  survivor carrier, promotion equations for regions/nodes/wires, canonical
  target, and the exact-wire partition/equivalence at the promoted target.
- `DoubleCutElimOccurrence.lean` owns the empty outer-cut occurrence equation
  and the exact permutation
  `hostOccurrences trace ++ [.child outer] ~ localOccurrences input trace.target`.

Both owners strict-compile with no proof holes. They use the existing intrinsic
symmetric `Rule.DoubleCut` design and introduce no relation variant.

## Exact next compiler theorem

The next owner should be
`VisualProof/Refinement/Implementation/DoubleCutElimCompile.lean`. It should
first package the two pointwise hypotheses below as focused promotion context
agreements, then prove this recursive compiler result (the names of those two
packages may be chosen locally, but their data must be exactly these maps):

```lean
theorem compileRegion_promotion
    (input : Concrete.Diagram)
    (inputWellFormed : input.WellFormed)
    {outer : Fin input.regionCount} {raw : Concrete.Diagram}
    (trace : Concrete.DoubleCutElimTrace input outer raw)
    (targetWellFormed : (DoubleCutElimTransport.Target trace).WellFormed)
    {rels : RelCtx}
    {sourceFuel targetFuel : Nat}
    (sourceRegion : Fin input.regionCount)
    (sourceSurvives :
      (DoubleCutElimTransport.Domain input outer trace.inner).survives
        sourceRegion = true)
    (notAboveTarget : ¬ input.Encloses sourceRegion trace.target)
    (sourceContext : Concrete.Elaboration.WireContext input)
    (targetContext : Concrete.Elaboration.WireContext
      (DoubleCutElimTransport.Target trace))
    (ambient : FiniteEquiv
      (Fin sourceContext.length) (Fin targetContext.length))
    (wireAgreement : ∀ index,
      targetContext.get (ambient index) = sourceContext.get index)
    (sourceExact : (sourceContext.extend sourceRegion).Exact sourceRegion)
    (targetExact :
      (targetContext.extend
        ((DoubleCutElimTransport.Domain input outer trace.inner).index
          sourceRegion sourceSurvives)).Exact
        ((DoubleCutElimTransport.Domain input outer trace.inner).index
          sourceRegion sourceSurvives))
    (sourceBinders : Concrete.Elaboration.BinderContext input rels)
    (targetBinders : Concrete.Elaboration.BinderContext
      (DoubleCutElimTransport.Target trace) rels)
    (binderAgreement : ∀ binder,
      targetBinders binder = sourceBinders
        ((DoubleCutElimTransport.Domain input outer trace.inner).origin binder))
    {sourceBody : Region sourceContext.length rels}
    {targetBody : Region targetContext.length rels}
    (sourceCompiled : Concrete.Elaboration.compileRegion? input sourceFuel
      sourceRegion sourceContext sourceBinders = some sourceBody)
    (targetCompiled : Concrete.Elaboration.compileRegion?
      (DoubleCutElimTransport.Target trace) targetFuel
      ((DoubleCutElimTransport.Domain input outer trace.inner).index
        sourceRegion sourceSurvives)
      targetContext targetBinders = some targetBody) :
    RegionIso ambient rels sourceBody targetBody
```

Inputs are the checked source and promoted target, a surviving region away from
the target site, exact source/target lexical contexts, the finite context-index
equivalence with identical underlying wire identifiers, survivor-origin binder
agreement, and both successful compiler equations. The output is precisely the
`RegionIso` needed for a child occurrence in either the host block or promoted
inner block.

The proof must recurse through `compileRegion?`, transport node compilation
through the pointwise wire/binder agreements, and transport child compilation
through the survivor index. The `notAboveTarget` premise is inherited by direct
children and excludes the one region whose local occurrences and exact-scope
wires change.

## Downstream owners

- `DoubleCutElimCompile.lean`: promotion context agreements and
  `compileRegion_promotion`.
- `DoubleCutElimRoot.lean`: assemble the target focus from the host and promoted
  inner occurrence blocks, use `exactWireEquiv`, and produce the root
  `OpenDiagramIso` plus contextual `Rule.DoubleCut` witness.
- `DoubleCutElimContext.lean`: transport the same focus construction through a
  nonroot context path and produce the nested contextual witness.
- `DoubleCutElim.lean`: connect the raw success trace, packing evidence, checked
  target, and representation result.
- `Refinement/Step/DoubleCut.lean`: expose successful `.doubleCutElim outer`
  execution refinement with the orientation-correct `Rule.DoubleCut` and
  `StateRepresents receipt.target`.

Root and nonroot cases share `compileRegion_promotion`; only their final
`OpenDiagramIso`/context-path assembly differs.

## Validation

- Strict Lean compilation passed for both completed owners.
- Focused builds passed for both completed owners.
- `audit-lean-authority.sh roster`, `rules`, `implementation`, and `proof`
  passed.
- Focused source scans found no holes, semantic dependencies, fixtures,
  matcher/search declarations, or forbidden declaration prefixes.
- `git diff --check` is part of the commit gate.
