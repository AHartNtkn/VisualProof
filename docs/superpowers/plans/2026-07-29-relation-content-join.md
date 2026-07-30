# Relation-content join implementation plan

**Goal:** Complete the accepted relation-content join soundness theorem without
relation-sever work or a second semantic authority.

**Architecture:** `RelationJoinSemanticTrace` remains the only ordered execution
receipt. Each step composes its canonical singleton-erasure receipt with either
the accepted insertion compilation's strict-ancestor receipt or a narrow
directional site-binder receipt for a co-scoped application. The latter fixes
retained host values and existentially chooses only fragment-local values; it
does not expose a bidirectional arbitrary-visible law. The canonical content
relation and ordered parameter values stay fixed. The result closes the dying
scope once, removes its proved endpoint-empty binder, and transports the
conclusion through its retained normalization. The rule layer exposes only the
already-planned `relation_join_sound`.

**Validation:** Start with a compiling negative probe for the absent public
theorem. Build each changed Lean owner and dependent rule module, then run
`lake build VisualProof`, `npm run formal:size`, proof-token and reification
audits, `git diff --check`, and read-only semantic/architecture reviews.

## Task 1: Establish the missing public boundary

- Create a session-local Lean probe importing `VisualProof.Rule.WireQuantifier`
  and checking `WireQuantifier.relation_join_sound`.
- Run Lean and retain the expected unknown-constant failure as evidence.

## Task 2: Compose one accepted relation application

- In the concrete semantic owner, recover the accepted insertion compilation.
- Factor the prior site at the dying scope.
- Use the step-owned singleton paired-frame receipt to replace the applied atom
  with intrinsic content under the canonical fixed content relation and
  parameter tuple.
- Align the erased frame with the insertion source frame.
- If the application is strictly inside the dying scope, use the insertion
  paired-frame strict-ancestor receipt.
- If it is co-scoped, use an internal directional generated-site binder
  certificate that preserves retained host values while choosing fragment-local
  witnesses.

## Task 3: Fold the enriched trace

- Induct on `RelationJoinSemanticTrace`.
- Carry the same canonical relation value and ordered parameter tuple through
  every `snoc` constructor.
- Produce only the common-scope body equivalence needed for the directional
  public join; do not claim a closed source/target equivalence.

## Task 4: Finish the accepted result

- Close the common dying scope once.
- Use `RelationJoinResult.bound_dying_endpoints` to remove the vacuous binder.
- Compose the retained identity-normalization equivalence.
- Add the existing planned `WireQuantifier.relation_join_sound` theorem and
  export it beside the other Task 8 soundness theorems.

## Task 5: Validate and commit

- Convert the negative probe into a compiling positive check.
- Add a semantic theorem over the maintained accepted same-scope fixture.
- Run focused and full builds, size and source audits, and diff validation.
- Obtain read-only semantic and architecture verdicts.
- Append foundation conformance and commit only task-owned paths.
