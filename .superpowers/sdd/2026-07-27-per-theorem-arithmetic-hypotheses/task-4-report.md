# Task 4 report

Status: complete.

Implemented:

- Rebuilt `successorShiftCarrierInductive` around its exact five hypotheses by reusing the exact `plusAssoc` shell and grounding `successorSingleValued` as a structural hypothesis handle.
- Rebuilt `succShiftS` to cite exact carrier support, ground `Nat(a)`, obtain the predecessor-output successor from `successorTotal`, and reconcile it with the supplied output through `plusSingleValued`.
- Rebuilt `commutativityCarrierInductive` around the exact six-hypothesis union by reusing `succShiftS`, grounding `zeroUnique`, and specializing unit/shift/support citations only over their actual primitives and antecedents.
- Rebuilt `plusComm` to cite exact commutativity support while retaining both public Nat premises.
- Removed stale seven-bundle positional indexing, direct standing-zero specialization, zero-uniqueness use from shift support, and every zero-existence path.
- Added exact contract assertions, zero-existence exclusion, per-hypothesis causal ablation, and transitive structural provenance checks with validated deiteration certificates.

Validation:

- `npx vitest run tests/theories/frege-statements.test.ts tests/theories/frege.test.ts tests/theories/reification.test.ts` — 3 files, 44 tests passed.
- `npm run typecheck` — passed.
- `git diff --check` — passed.

Concerns: none.

## Review round 1

Status: fixed.

Rebuilt the decisive Task-4 validation:

- Namespaced proof provenance by proof half and state and starts every exact
  premise at backward RHS state 0.
- Tracks independent structural ownership branches through receipt-validated
  wire transport, iteration copies, wire-join specialization, unfolded
  descendants, and certificate-validated deiteration.
- Accepts only direct certified use, a specialized certificate-consumed
  obligation, or a specialized fact in the independently verified meeting
  state. Copy creation alone is not success.
- Added a regression oracle that truncates immediately after the exact
  `plusBase` iteration and requires rejection.
- Replaced endpoint deletion as the decisive commutativity Nat evidence.
  `commutativityCarrierInductive` fixed-right `Nat(b)` and `plusComm`
  `Nat(a)`/`Nat(b)` are selected by ordered Nat arguments, with public
  individuals derived from the ordered `Plus(a,b,o)` arguments, and must pass
  the same structural proof-path oracle.

Red evidence:

- Before the oracle rebuild, the truncated `plusBase` trace ending at an
  unused iteration copy was accepted (`expected [Function] to throw an
  error`).
- During reconstruction, the strengthened Nat oracle rejected public
  `plusComm Nat(a)` until certificate-consumed unfolded carrier obligations
  were recognized as the required consumed-obligation terminal.

Green validation:

- `npx vitest run tests/theories/frege-statements.test.ts tests/theories/frege.test.ts tests/theories/reification.test.ts`
  — 3 files, 44 tests passed.
- `npm run typecheck` — passed.
- `git diff --check` — passed.

The proof oracle remains test-local in `frege.test.ts`: its trace, selection,
certificate, and theorem-shape helpers form one cohesive arithmetic validation
layer and have no production consumer.
