# Task 3 report — canonical theorem replacement soundness

## Status

Blocked before the public receipt theorem. The generic paired-splice
presentation, its `PinnedOccurrence` specialization, proof-dependent boundary
witnesses, and both strict alias-partition examples compile. The repository
does not yet contain the cross-partition paired compiler simulation needed to
prove `applyTheorem_sound` without assuming the result.

Foundation record:
`/tmp/visualproof-task3-foundation-20260716.md`.

## Implemented declarations

### Generic paired splice presentation

`VisualProof.Diagram.Splice.Input.TwoInputPresentation source target` records:

- equality of the retained checked frames;
- equality of the distinguished sites under the induced finite cast;
- equality of ordered pattern-boundary arities; and
- positional equality of source and target attachments.

Its projections establish the reusable structural facts required by a paired
compiler simulation:

- `regionMap_frameRegion` and `regionMap_site`;
- `QuotientClassesRelated`, `quotientWire_related`, and
  `attachment_quotient_related`;
- coalesced-frame root, region-count, node-count, region-payload, and
  node-payload equalities with explicit dependent casts.

The presentation deliberately relates quotient classes through shared retained
frame wires. It does not select a refinement map in either direction, so it
supports incomparable and strictly coarser/finer alias partitions.

### Named specialization

`PinnedOccurrence.twoInputPresentation` specializes the generic presentation
to the canonical source-side and replacement-side inputs produced from one
decomposition. It proves the common frame/site and positional attachment facts
definitionally while retaining the supplied boundary-arity equality.

### Proof-dependent boundary construction

`proofDependentBoundaryWitness_forward` and
`proofDependentBoundaryWitness_backward` consume the active open-diagram
denotation through the local law before selecting the opposite boundary
assignment. They use `orderedBoundaryRelation`, which is intentionally
many-to-many and position based.

There is no `CanonicalLocalReplacementSimulation`, compatibility adapter, or
structure field containing a preselected `DirectionalBoundaryWitness`.

### Strict partition examples

`StrictAliasPartitionExamples.equalityFineBoundary` has two distinct external
classes and a body equation proving the two positional values equal.
`equalityFineBoundary_entails_aliased` extracts that equality from active body
denotation and only then constructs the aliased target assignment.

The two examples cover:

- forward simulation from the fine source boundary to the strictly coarser
  aliased target boundary; and
- backward simulation with the strictly coarser boundary on the source side.

Neither theorem statement has an unconditional equality premise.

### Theorem payload laws

`theoremPayload_forward_local` and `theoremPayload_backward_local` recover the
registered schema implication from `theoremSidesMatch` and
`TheoremSchema.Valid`. `contextualizeCitation` remains the single abstract
variance lift for the four orientation/direction cases.

## Exact missing lemma and owner

The smallest missing semantic result belongs in
`VisualProof/Diagram/Concrete/Subgraph/Splice.lean` alongside
`TwoInputPresentation`:

```lean
theorem TwoInputPresentation.compiledSpliceSourceOpen_entails
    (presentation : TwoInputPresentation source target)
    (hsource : spliceChecked signature source = .ok sourceResult)
    (htarget : spliceChecked signature target = .ok targetResult)
    (sourceBoundary : List (Fin source.frame.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (source.frame.val.wires wire).scope = source.frame.val.root)
    (direction : ConcreteElaboration.SimulationDirection)
    ...
    (localLaw : direction.Entails
      (source.pattern.denote model named sourcePatternArgs)
      (target.pattern.denote model named targetPatternArgs)) :
    direction.Entails
      (denoteOpen model named
        (compiledSpliceSourceOpen source hsource sourceBoundary sourceRoot)
        sourceArgs)
      (denoteOpen model named
        (compiledSpliceSourceOpen target htarget targetBoundary targetRoot)
        targetArgs)
```

The omitted arguments are only the casted target boundary/root and positional
argument transports determined by `presentation`; they must not include a
preselected semantic boundary witness.

Its proof must instantiate the shared
`ConcreteElaboration.ConcreteSemanticSimulation` over the two plug layouts,
using the common frame/site for regular occurrences, the related quotient
classes for exact compiler contexts, and a distinguished-site kernel that
consumes active source pattern denotation before constructing a coarser target
assignment. Existing splice theorems are one-input results: they compare each
compiled source with its own output or coalesced frame, and therefore cannot
derive this cross-partition implication.

Once that lemma exists, `applyTheorem_realizes`, the payload-local laws,
`contextualizeCitation`, and
`SuccessfulReceiptSound.of_realized_operational` are sufficient to finish the
exact public theorem:

```lean
applyTheorem_sound :
  SuccessfulReceiptSound context orientation input
    (.theorem theoremIndex selection args direction payload registered) receipt
```

## Validation

The current partial implementation is internally green:

```text
lake build VisualProof.Diagram.Concrete.Subgraph.Splice
Build completed successfully (35 jobs).

lake build VisualProof.Rule.Named VisualProof.Rule.Soundness.HighLevel
Build completed successfully (45 jobs).
```

Source inspection found no `sorry`, `admit`, custom `axiom`, compatibility
witness, or displaced `CanonicalLocalReplacementSimulation` in the task-owned
files. `git diff --check` is included in the final commit validation.

## Self-review

- The new structural relation does not assume that either quotient partition
  refines the other.
- Positional boundary order and repeated positions are retained throughout.
- The strict examples obtain alias equality from active denotation.
- The old preselected-witness ownership model is absent.
- The public theorem is intentionally not declared because doing so without the
  paired compiler lemma would require an axiom, `sorry`, or a circular premise.

## Exact unblock

Implement and kernel-check
`TwoInputPresentation.compiledSpliceSourceOpen_entails` as the shared paired
compiler simulation described above. No user product decision or external
tooling input is missing; this is remaining formalization work.
