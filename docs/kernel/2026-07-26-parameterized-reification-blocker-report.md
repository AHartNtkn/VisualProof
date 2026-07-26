# Parameterized Reification Blocker: Incident and Resolution Report

Date: 2026-07-26  
Branch: `worktree-signature-indexed-wires`  
Phase: Phase 2, relational Frege theory rebuild  
Status: historical diagnosis corrected; the preserved theorem-bridge experiment
passes, but its definition-store authority was subsequently superseded by
commit `a7437a1`

## Executive summary

Task 6 initially appeared blocked because a parameterized reification could not
be reconstructed *in situ* from primitive structural moves without leaving an
extra source occurrence or capture/identity residue.

The relevant figure had the form

```text
D(P, captures) := forall x. P(x) <-> S(x, captures)
```

where `P : rel(iota)` was the induction carrier and `captures` were theorem-local
primitive relation wires such as `Zero`, `Succ`, and `Plus`.

The direct construction repeatedly encountered three real gates:

1. `atomSpawn` could create the needed `P(x)` only in a negative region.
2. `iteration` could copy only into the source region or its descendants, not
   across the sibling implications of the biconditional.
3. A dominating negative source could be copied into a positive consequent but
   could not then be erased.

The definition-ref route encountered a different form of the same problem:
`refSpawn` minted fresh capture wires at the spawn scope. At the attempted
positive site those wires could not be joined to the theorem's outer captures;
moving the construction through a double cut made the join possible only at the
cost of unerasable identity/capture residue.

Those observations were real for the attempted *local reconstruction*. The
conclusion drawn from them—“the existing kernel cannot support the required
parameterized reification”—was not justified.

The omitted route was ordinary theorem citation, which the design already named
as the way to amortize assertion-form/reified-form and Eq sequences. A bridge
theorem can be verified once at root scope:

```text
D(P, captures) and P(a)
    implies
D(P, captures) and S(a, captures)
```

with ordered boundary

```text
[P, ...captures, a]
```

Its proof uses eight existing primitive steps. Once verified, theorem citation
matches the complete pinned occurrence and splices the other side directly onto
the caller's existing boundary wires. It therefore does not reconstruct the
biconditional across the caller's sibling regions and does not mint replacement
capture wires. A nested right-identity experiment using outer `Zero`, `Plus`,
and `a` wires reached an independently constructed exact endpoint, removed the
temporary ref and `P` wire, passed `checkTheorem`, and required no kernel or app
change.

This corrected one false blocker diagnosis. It did **not** finish the arithmetic
proofs. It also did not establish that definition-store reification spawning was
the correct final architecture. Commit `a7437a1` subsequently superseded that
authority with strongest-sound sever/join rules, so the bridge implementation
described here is preserved as architectural evidence, not as the current
implementation recommendation.

## 1. Context and exact proof obligation

The Phase-2 arithmetic plan required the induction proofs for right unit,
associativity, successor shift, and commutativity to instantiate the `forall P`
inside `Nat` with an explicit unary carrier.

The four carrier assertions in the implementation at the time were:

### Right identity

```text
R(x) :=
  forall z,o.
    Zero(z) and Plus(x,z,o)
      implies o = x
```

Captured boundary:

```text
[P, Zero, Plus]
```

### Associativity

```text
A(x) :=
  forall b,c,t,o,u.
    Plus(x,b,t) and Plus(t,c,o) and Plus(b,c,u)
      implies Plus(x,u,o)
```

Captured boundary:

```text
[P, Plus]
```

### Successor shift

```text
Shift(x) :=
  forall r,rs,o,os.
    Succ(r,rs) and Plus(x,r,o) and Succ(o,os)
      implies Plus(x,rs,os)
```

Captured boundary:

```text
[P, Succ, Plus]
```

### Commutativity

```text
C(x) :=
  forall r,o.
    Plus(x,r,o)
      implies Plus(r,x,o)
```

Captured boundary:

```text
[P, Plus]
```

For a generic carrier `S`, the required reification definition was:

```text
D(P, captures) :=
  forall x. P(x) <-> S(x, captures)
```

The induction helper statements already carried a ref
`D(P, theorem-local captures)` pinned to their outer primitive wires. The proof
still needed to move repeatedly between `P(a)` and `S(a, captures)` while
retaining the ref as authority and eventually cleaning the proof-local material.

## 2. The presumed blocker

The failed work treated each use of the reification as though the full
biconditional had to be rebuilt locally from primitive rules.

### 2.1 Constructing the two `P(x)` occurrences directly

A biconditional contains two sibling implication cuts:

```text
P(x) -> S(x)
S(x) -> P(x)
```

Forward `atomSpawn` requires a negative region. This permits the occurrence of
`P(x)` in an implication antecedent, but the reverse consequent is positive.

A direct positive spawn failed with:

```text
spawning requires a negative region; 'dc_4' is positive
```

Trying to copy the legal occurrence from the forward antecedent into the reverse
consequent failed because the two branches are siblings:

```text
iteration target 'dc_8' must lie within the source region 'dc_5'
```

This is the intended ancestry gate in
[`iteration.ts`](../../src/kernel/rules/iteration.ts): iteration targets must be
the source region or its descendants.

### 2.2 Using a dominating negative source

The next attempt spawned `P(x)` in the negative reverse antecedent, where it
dominated the positive reverse consequent. Iteration into the consequent
succeeded.

The source then had to disappear to recover the exact biconditional. Forward
erasure rejected it:

```text
erasure requires a positive region; 'dc_3' is negative
```

Deiteration does not solve this ownership problem. It removes a descendant copy
justified by a matching ancestor; it does not remove the ancestor source.
Double-cut introduction also preserves the source's effective polarity rather
than making it erasable.

The clean-branch standalone probe for this case was the only scratch probe that
remained independently executable after the arithmetic WIP was stashed. It
confirmed both the positive-spawn rejection and the surviving negative source.

### 2.3 Spawning a definition ref and attaching captures

The alternative route used the stored exact definition:

1. spawn a reification ref;
2. unfold it;
3. retarget a copy through identities onto supplied captures;
4. fold the supplied-capture copy;
5. erase the original material.

The fold itself succeeded. The obstruction was capture ownership and cleanup.

At a positive helper conclusion, `refSpawn` created fresh ref arguments scoped
at that positive region. Joining a fresh capture to an outer theorem primitive
failed because forward `wireJoin` requires the inner wire's scope to be
negative:

```text
joining wires requires the inner wire's scope to be negative;
'r4' is positive
```

Moving the work through a double-cut shell allowed identity-retargeted copying
and folding, but left two identities in the negative annulus. The attempted
cleanup gates then rejected:

```text
erasure requires a positive region; 'dc' is negative
```

and:

```text
annulus 'dc' must contain exactly one child cut and nothing else
```

Spawning the source in a negative ancestor inverted which operation was legal:
capture joins became possible, but the negative source ref could not be erased.
Backward join did not supply an escape because its inner-scope gate is the dual
positive requirement.

### 2.4 The original conclusion

The experiment report summarized the issue as:

> The exact parameterized reification helper cannot be constructed and folded
> without an extra source or residual identity/capture frame.

That statement accurately described the attempted local constructions. It was
then overgeneralized into:

> Existing Phase-1 primitives cannot support the Task-6 parameterized
> reification.

That second statement was the invalid blocker diagnosis.

## 3. Why the original evidence was insufficient

Three evidence defects mattered.

### 3.1 It tested one construction strategy as though it exhausted the design

The experiments tested direct primitive reconstruction and ref/unfold/fold
cleanup. They did not test ordinary theorem citation.

This omission was material. The controlling specification explicitly said that
the assertion-form/reified-form pairing and Eq lemmas were ordinary recorded
theorems reused through theorem-to-theorem citation. The Phase-2 prefix in the
branch contained only:

```text
ordinaryEqualityContradiction
existsProp
```

The required reification/Eq theorem layer had never been implemented. Treating
its absence as a kernel limitation reversed the responsibility boundary.

### 3.2 Two probes did not reproduce from the clean branch

The cross-sibling/fold probes imported partial Task-6 modules that were later
preserved only in WIP stash:

```text
3516cf25e7cca13123d9a4508759173183cd7c00
```

After stashing, rerunning them from the clean worktree failed at module
resolution before reaching the claimed rule diagnostics. Those probes remained
useful historical traces, but they were not standalone clean-checkout evidence.

The report originally pointed only to `/tmp` paths. That made the evidence both
ephemeral and inaccessible outside the originating session.

### 3.3 The report did not state the exact missing capability

“Parameterized reification is blocked” conflated three different questions:

1. Can the full biconditional be rebuilt locally from blank?
2. Can a stored ref with fresh arguments be retargeted and cleaned locally?
3. Can a previously verified theorem rewrite an exact pinned
   ref-plus-application occurrence at a nested caller site?

The probes supported negative answers only for the particular attempted forms of
questions 1 and 2. The successful bridge answered question 3 positively.

## 4. The theorem-citation bypass

### 4.1 Bridge theorem schema

For each unary reification authority, define two ordinary theorems:

```text
D(P, captures) and P(a)
  -> D(P, captures) and S(a, captures)

D(P, captures) and S(a, captures)
  -> D(P, captures) and P(a)
```

Both theorem sides use the same ordered boundary:

```text
[P, ...captures, a]
```

Concrete boundary orders were:

| Carrier | Boundary |
| --- | --- |
| Right identity | `[P, Zero, Plus, a]` |
| Associativity | `[P, Plus, a]` |
| Successor shift | `[P, Succ, Plus, a]` |
| Commutativity | `[P, Plus, a]` |

A separate unary Eq bridge used:

```text
[target, source, a]
```

with the target positions aliased on the result boundary after identity
normalization.

### 4.2 The eight-step primitive proof

Each directional assertion/reification bridge was verified with the same eight
surviving kernel steps:

1. **Iteration:** copy the standing reification ref `D(P, captures)`.
2. **Unfold:** expose the copied definition
   `forall x. P(x) <-> S(x, captures)`.
3. **Wire join:** bind its quantified `x` to the supplied boundary individual
   `a`.
4. **Double-cut elimination:** expose the now individual-bound biconditional.
5. **Erasure:** remove the unused implication direction.
6. **Deiteration:** discharge the selected branch premise against the supplied
   root occurrence (`P(a)` or the complete pinned `S(a, captures)`).
7. **Double-cut elimination:** expose the desired branch consequence.
8. **Erasure:** remove the consumed supplied occurrence.

The original ref remains on both sides as the authority. No new proof rule,
macro, computation layer, or primitive second-order-instantiation step is used.

### 4.3 Why citation avoids the local topology obstruction

The crucial distinction is that theorem application does not inline these eight
steps into the caller.

The kernel first verifies the bridge theorem once. A citation then:

1. extracts an exact occurrence of one theorem side;
2. compares its canonical form with the theorem side under the ordered boundary
   arguments;
3. splices the other verified side directly onto those caller-supplied wires;
4. removes the matched occurrence.

Consequently:

- the caller does not transport `P(a)` between sibling implication cuts;
- the caller does not need a dominating negative source;
- the caller does not mint replacement `Zero`, `Succ`, or `Plus` captures;
- ordered boundary pins attach the result to the already-scoped outer captures;
- the bridge's internal source and branch cleanup was discharged once during
  theorem verification.

This is exactly the distinction between proving a derived rule and reusing it.
The direct experiments attempted to re-prove the derived rule at every
arithmetic use site.

### 4.4 Nested supplied-capture validation

The focused validation constructed a nested universally quantified site with
outer wires:

```text
Zero : rel(iota)
Plus : rel(iota,iota,iota)
a    : iota
```

Inside its positive body it placed:

```text
D(P, Zero, Plus)
P(a)
```

It cited the right-identity bridge with arguments:

```text
[P, Zero, Plus, a]
```

After citation, it:

1. erased the now-consumed reification ref in the positive region;
2. removed the endpoint-free temporary `P` wire with `vacuousElim`.

The result was canonically identical to an independently drawn right-identity
assertion:

```text
forall z,o.
  Zero(z) and Plus(a,z,o)
    implies o = a
```

The focused test also showed that omitting the `Plus` capture made citation fail
on attachment/boundary arity, and that removing the bridge's individual-binding
`wireJoin` made `checkTheorem` fail.

### 4.5 Exact scope of the bypass

The bridge did not derive `D(P, captures)` from a bare assertion or from the
empty sheet. Its theorem sides both contained the same standing ref, and the
nested validation began with that ref already attached to the caller's supplied
capture wires.

That was sufficient for the induction-helper obstruction being tested because
the helper statements already included the pinned reification ref. It bypassed
the repeated local conversion between:

```text
P(a)
```

and:

```text
S(a, captures)
```

under that standing authority.

It did not independently solve premise-free reification existence or prove that
`refSpawn` could create the pinned ref at every eventual consumer site. Those
questions must not be folded into the bridge result. The later `a7437a1`
specification addresses premise-free reification through strongest-form
severing instead of definition-store spawn authority.

## 5. Verified result

The preserved experiment was rerun on 2026-07-26 after the blocker report was
challenged:

```text
npx vitest run \
  tests/theories/reification-bridges.test.ts \
  tests/theories/reification.test.ts \
  tests/theories/frege-statements.test.ts
```

Result:

```text
3 test files passed
28 tests passed
```

Type checking:

```text
npm run typecheck
```

Result:

```text
tsc --noEmit
passed
```

Scope audit:

```text
git diff -- src/kernel tests/kernel src/app
```

Result: empty.

This evidence establishes:

- the ordinary bridge theorems verify under the then-current kernel;
- exact theorem citation can use theorem-local outer captures;
- the representative nested endpoint cleans exactly;
- the presumed local-construction obstruction is not a general
  theorem-reuse obstruction;
- no Phase-2 kernel change was required for this bypass.

It does **not** establish:

- completion of the four induction-heavy arithmetic proofs;
- completion of all eight Task-6 arithmetic theorems;
- that every required proof-site polarity and direction was exercised;
- that the interrupted bridge implementation should be committed;
- that definition-store reification spawning is the current architecture.

## 6. Subsequent architectural supersession

While the bridge implementation was still uncommitted, commit `a7437a1`
(`docs: restate wire-quantifier pair at strongest sound form`) changed the
authoritative umbrella specification.

That commit says the earlier atomic-only sever/join formulation was weaker than
the strongest rule sound in full higher-order models. It supersedes the
definition-store reification-spawn authority with:

- strongest-form severing as relation-level existential introduction over exact
  drawn content; and
- strongest-form `wireJoin` as relation-level universal elimination by grounding
  a relation wire to exact drawn content.

Under that revised specification:

```text
exists P. P <-> G
```

is derived directly from the wire-quantifier pair rather than obtained through a
definition ref with special spawn authority.

Therefore the theorem-citation bridge remains important evidence about the
false blocker diagnosis and the power of exact pinned citation, but its
definition-ref authority is not the current target design. Any continuation
must first plan and land the `a7437a1` Phase-1 correction; the interrupted
Phase-2 bridge files must not be treated as current production work merely
because their tests pass.

## 7. Root cause and process corrections

The technical root cause was not a missing kernel capability in the tested
architecture. It was rebuilding a reusable derived theorem locally and omitting
the citation path named by the design.

The evidence-handling root cause was treating session-local scratch files as the
reporting surface. The corrected standard is:

1. Durable architecture findings go under `docs/`.
2. A blocker report states the exact formula, boundary, scope, polarity, rule
   sequence, and diagnostic.
3. Every cited reproducer is classified as:
   - clean-checkout executable;
   - dependent on preserved WIP; or
   - historical observation only.
4. A failure of one construction strategy is not generalized until every
   architecture-prescribed authority path has been tested.
5. A successful bypass is reported with both its demonstrated scope and its
   unproved remainder.
6. If the authoritative specification changes during an experiment, production
   work stops and the report separates the historical result from the new
   governing design.

## 8. Repository state at report creation

At the time this report was written:

- the bridge implementation and its tests were uncommitted, interrupted WIP;
- the earlier arithmetic WIP remained preserved in stash
  `3516cf25e7cca13123d9a4508759173183cd7c00`;
- the unrelated user file remained preserved in stash
  `3ec32f9711e19108ed3d89d8b00474a789e4ddb5`;
- no kernel or app path was modified by the bridge experiment;
- commit `a7437a1` was the branch head and governed subsequent design work.

The durable conclusion is narrow:

> The original direct-construction blocker was real for the attempted local
> sequences, but the conclusion that existing theorem machinery could not
> bridge reified and assertion forms was false. Exact boundary-pinned theorem
> citation provided that bridge without a kernel change. A later specification
> revision then superseded the definition-store authority on which that
> particular bridge formulation was based.
