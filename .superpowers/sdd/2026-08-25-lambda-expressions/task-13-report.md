# Task 13 report: remaining Lean Lambda rule surface

## Outcome

Implemented the remaining Lambda-owned Fission/Fusion, Congruence, HeadStrip,
and AnchoredWire relations without changing the existing Spawn, TermLeaf,
Conversion, or FreeVariableIdentity relations.

- Fission records an intrinsically bound-closed selected occurrence, its exact
  capture-avoiding residual, the native interface, and the fresh binary bridge.
- Fusion records the private output/free-slot bridge and the exact
  consumer-first, producer-first-occurrence carrier construction used by the
  TypeScript operation. Repeated physical wires remain distinct consumer
  columns where TypeScript keeps them and producer aliases select the same
  first/same-position columns as TypeScript.
- Congruence records a covered common positional interface, aliased physical
  carriers, beta-eta evidence, two distinct output wires, and both output
  derived-scope depth guards before keeping the left output.
- HeadStrip records aligned head-normal spines with the same bound rigid head,
  ordered non-reflexive argument equations, and first-occurrence physical-wire
  compaction. Its universal soundness theorem uses the model's exact rigid-head
  argument-reflection field in the forward direction and beta-eta soundness of
  the reconstructed rigid skeleton in the reverse direction.
- AnchoredWire split and contract carry closed witnesses, exact endpoint
  partitions, derived-scope/availability premises, proof-relevant global
  endpoint addresses, exact old-scope completion requests, canonicality, and
  two-endedness. Both directions use one nested multi-site rewrite witness with
  an exact descendant replacement followed by an authoritative deepest-first
  completion sequence.
- Every relation transports over open-diagram isomorphism and has exact
  source-indexed forward and backward runners. All five evidence cases are
  registered in `Step.Evidence`, aggregate soundness, executable evidence, and
  aggregate execution completeness.

## Pulled-in diagram and model API

`VisualProof.Diagram.ScopedRewrite` adds stable external/internal wire
addresses, exact endpoint addresses, proof-relevant scoped regions and
replacements, and exact `completeWireEnds` plans. Each completion pin proves
its current address, exact destination scope, the TypeScript scope-enclosure
gate, and the rebuilt intermediate. Counts are calculated from current
incidences and requests are sorted deepest-first so later addresses remain
authoritative.

`VisualProof.Diagram.NestedScopedRewrite` composes region, wire, and endpoint
addresses through the selected ancestor, same-region prefix, descendant
context, and primary site. Its indexed `NestedOccurrence.ScopedRewrite`
rebuilds the primary target through the existing recursive `Region` and then
owns the complete ordered destination plan through to the public target body.
This is occurrence evidence over the existing diagram representation, not a
second diagram representation.

`VisualProof.Model` now has only the aligned bound-rigid-head reflection law
needed by HeadStrip. `Lambda.canonicalModel_rigidHead_args_reflect` proves the
law for the beta-eta quotient using representatives,
`canonicalModel_eval_eq_quote`, `quote_eq_iff`, and
`rigidHead_args_bindFree_bound`; `Model.canonical` supplies the inhabited
canonical diagram model.

## Theorem-driven RED/GREEN evidence

For every RED below, the theorem statement and its complete definition
dependency closure elaborated first; the sole temporary admission was the
named owning production theorem. GREEN used the same command after replacing
that admission, and the declaration then kernel-checked without an admission
warning.

### Canonical rigid-head reflection

Owning theorem: `Lambda.canonicalModel_rigidHead_args_reflect`.

```text
lake env lean VisualProof/Model.lean
```

RED reported `declaration uses sorry` at the production theorem. GREEN passed
after choosing quotient representatives, transporting both evaluations to
quotes, reflecting quote equality to beta-eta equivalence, applying
`rigidHead_args_bindFree_bound`, and transporting each argument evaluation
back through `canonicalModel_eval_eq_quote`.

### Rigid-head reconstruction

Owning theorem: `Lambda.rigidBoundSkeleton_bind_arguments`.

```text
lake env lean VisualProof/Lambda/Reduction.lean
```

RED reported the single owning admission. GREEN passed with the eta-long
skeleton, substitution-through-eta-long-body lemma, prefix-closing beta-eta
proof, and ordered `List.Forall₂` argument reconstruction.

### Fission

Owning theorems: `Fission.Local.sound_iff` and `Fission.sound`.

```text
lake env lean VisualProof/Rule/Soundness/Lambda/Fission.lean
```

The local theorem reached RED after the complete capture-avoiding relation;
GREEN reconstructed the expanded environment, evaluated the selected producer,
used `model.eval_bindFree` plus the stored reconstruction equality, and
transported untouched items through the retaining renaming. The final direct
open theorem was separately re-RED after its exact global relation was fixed;
Lean reported `Fission.lean:241:8: warning: declaration uses sorry`. GREEN
passed by lifting `Local.sound_iff` through the occurrence context and both
open isomorphisms.

### Fusion

Owning theorems: `Fusion.Local.sound_iff` and `Fusion.sound`.

```text
lake env lean VisualProof/Rule/Soundness/Lambda/Fission.lean
```

The local theorem reached RED with the producer/consumer bridge, carrier maps,
and merged term complete. GREEN used `eval_mapFree`, `eval_bindFree`, the exact
consumed slot, and retained-environment equalities in both directions. The
global theorem was separately re-RED after exact old-scope completion became a
production premise; Lean reported the owning warning at the then-current line
484. GREEN lifted the local equivalence through the occurrence, then composed
the completion-plan equivalence and target isomorphism.

### Congruence

Owning theorems: `Congruence.Local.sound_iff` and `Congruence.sound`.

```text
lake env lean VisualProof/Rule/Soundness/Lambda/Congruence.lean
```

The local theorem reached RED with the covered aliased carrier and beta-eta
certificate complete. GREEN evaluated both terms through the common carrier,
used `model.betaEta_sound`, and collapsed/restored the two output values. The
final global theorem was re-RED after adding both exact derived-scope guards;
Lean reported `Congruence.lean:192:8: warning: declaration uses sorry`.
GREEN passed through occurrence-context and open-isomorphism transport.

### HeadStrip

Owning theorems: `HeadStrip.Local.sound_iff` and `HeadStrip.sound`.

```text
lake env lean VisualProof/Rule/Soundness/Lambda/HeadStrip.lean
```

The local theorem reached RED only after physical compaction, ordered argument
selection, the Model reflection field, its canonical proof, and rigid-skeleton
reconstruction were complete. GREEN reflects whole rigid-head equality into
each prefix-closed argument equality, emits exactly the non-reflexive compacted
equations, and reconstructs whole equality from all argument equations using
beta-eta soundness. The final completion-aware open theorem was separately
re-RED; Lean reported its owning warning at the then-current line 795. GREEN
composed the local, contextual, completion-plan, and isomorphism equivalences.

### AnchoredWire

Owning theorem: `AnchoredWire.sound`, covering both `split` and `contract`.

```text
lake env lean VisualProof/Rule/Soundness/Lambda/AnchoredWire.lean
```

All exact address composition, endpoint partition, closed-witness availability,
primary factorization, and completion-plan helpers were complete before RED.
Lean reported the sole owning warning at the then-current line 621. GREEN
passed by transporting the selected closed witness value through reachable
contexts, proving split/contract as inverse equality factorizations, applying
beta-eta soundness for convertible closed witnesses, composing every exact pin
insertion equivalence, and transporting through the source/target isomorphisms.

## Files

Model and Lambda reduction support:

- `VisualProof/Model.lean`
- `VisualProof/Lambda/Reduction.lean`

Occurrence/rewrite API:

- `VisualProof/Diagram/ScopedRewrite.lean`
- `VisualProof/Diagram/NestedScopedRewrite.lean`
- `VisualProof/Diagram/Semantics/ScopedRewrite.lean`

Lambda relations, soundness, and exact execution:

- `VisualProof/Rule/Lambda/Fission.lean`
- `VisualProof/Rule/Lambda/Congruence.lean`
- `VisualProof/Rule/Lambda/HeadStrip.lean`
- `VisualProof/Rule/Lambda/AnchoredWire.lean`
- `VisualProof/Rule/Soundness/Lambda/Fission.lean`
- `VisualProof/Rule/Soundness/Lambda/Congruence.lean`
- `VisualProof/Rule/Soundness/Lambda/HeadStrip.lean`
- `VisualProof/Rule/Soundness/Lambda/AnchoredWire.lean`
- `VisualProof/Rule/Executable/Lambda/Fission.lean`
- `VisualProof/Rule/Executable/Lambda/Congruence.lean`
- `VisualProof/Rule/Executable/Lambda/HeadStrip.lean`
- `VisualProof/Rule/Executable/Lambda/AnchoredWire.lean`

Public registration:

- `VisualProof/Rule/Lambda.lean`
- `VisualProof/Rule/Soundness/Lambda.lean`
- `VisualProof/Rule/Executable/Lambda.lean`
- `VisualProof/Rule/Step.lean`
- `VisualProof/Rule/Soundness.lean`
- `VisualProof/Rule/Executable/Step.lean`

## Validation

```text
lake build
Build completed successfully (151 jobs).

rg -n '\bsorry\b' VisualProof --glob '*.lean'
no matches

git diff --check
clean
```

Focused GREEN recompilation also passed for every new relation, soundness, and
executable module. The final Task 13 modules emit no linter warning; the full
build replays established warnings in pre-existing modules.

## Self-review

- Compared each relation to the current Task 7 TypeScript implementation,
  including fission's no-op native completion case, Fusion's same-position
  alias preference, Congruence's two output scope guards and left survivor,
  HeadStrip's syntactic reflexivity filter and first-occurrence compaction, and
  AnchoredWire's availability/shielding gates.
- Confirmed completion witnesses retain the old derived scope, reject a scope
  that does not enclose current incidences, insert exactly the computed number
  of unary identities, and rebuild one final canonical two-ended target.
- Confirmed AnchoredWire contraction excludes the removed output wire from its
  touched-wire completion set, matching the TypeScript loop.
- Confirmed every exact runner returns the description-owned target forward and
  the description-owned canonical source backward, with the public theorem
  accounting only for declared open-diagram isomorphism.
- Confirmed all four previously registered Lambda families remain unchanged in
  Step evidence, soundness, and execution matches.
- Confirmed there are no compatibility layers, alternate term/diagram
  representations, fixture theorems, examples, checks, or admissions.

## Concerns

None. Fresh identifiers and incidental item ordering are represented through
the existing public open-diagram isomorphism boundary; all semantic operands,
physical carrier aliases, region addresses, endpoint choices, scope guards,
and completion destinations remain proof-relevant in the source-indexed
operation witness.
