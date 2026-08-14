# Random Theorem Generation — Design

Date: 2026-08-14
Status: approved in discussion; awaiting spec review

## Goal

Add a mode to the app that generates a random true theorem for the user to
prove by backward reasoning. The user picks a generation family from a menu,
adjusts a few knobs, generates a problem, and commits it as the edit-mode
diagram; from there the existing "Prove backward" flow takes over unchanged.

The first two families both target classical propositional tautologies and
implement two independent generation methods:

1. **Generate-and-shrink** — sample a random formula, keep tautologies, shrink
   away irrelevant subformulas until every remaining piece is load-bearing.
2. **Kernel rule walk** — apply real kernel proof rules forward from the blank
   sheet, so the result carries an actual derivation in the move system.

The two families are architecturally separate pieces intended as starting
points for later families. A minimal-proof search over the kernel move system
verifies each generated problem and labels its difficulty.

## Decisions made during design

- After generation, the diagram lands in **edit mode** (replacing the edit
  diagram); the user clicks "Prove backward" themselves. No new mode-entry
  path.
- Each family exposes **a few knobs** with prefilled defaults (no single
  difficulty slider).
- The rule walk operates at the **kernel level** (real rule applications on
  `Diagram` values), not on formula ASTs. Forward and backward orientation
  already exist in the kernel; the kernel itself needs no modification.
- The minimal-proof search is **in scope** and is used to **verify and label**
  difficulty only — it does not filter generation and its found proof is not
  stored for hints.
- Tautology checking is **truth-table evaluation** (no SAT solver).
- The propositional connective set is **{¬, ∧}** only — complete, and native
  to the diagram language (cuts + juxtaposition). No ∨/→/↔ in sampled
  formulas. A possible future family treats ↔ as equality over propositions;
  it is out of scope here but slots into the family registry.

## Architecture

Three isolated modules plus a thin UI panel. None touches the kernel.

```
src/generate/
  index.ts        family registry (GeneratorFamily, KnobSpec, GeneratedProblem)
  prop/           propositional core + family A (pure, no kernel imports
                  except the formula pipeline at the output boundary)
  walk/           family B: kernel forward walk
  search/         minimal-proof search + candidate-step enumerator
src/app/generate-entry.ts   UI panel (modeled on formula-entry.ts)
```

Kernel facts the design relies on (verified against the code):

- There is no separate "insertion" rule; insertion is `erasure` with backward
  orientation. Orientation flips polarity gates only, never the
  transformation (`src/kernel/proof/step.ts`, `src/kernel/rules/erasure.ts`).
- `PrimitiveStepRecorder` (`src/theories/record.ts`) applies and logs steps
  from a starting side, handles stale-id renaming, auto-pins on
  `ScopePreservationError`, and tidies; `src/theories/logic.ts` is the worked
  example. This is the walk's harness.
- No move enumerator or proof search exists anywhere;
  `applicableActions` (`src/app/actions.ts`) only classifies an
  already-chosen selection. The enumerator is new work.
- `sameDiagram`/`diagramIso` (`src/kernel/diagram/canonical/iso.ts`) decide
  exact diagram isomorphism via joint color refinement. There is no canonical
  string-form function anywhere in the kernel, so the search memoizes via an
  iso-invariant digest confirmed by `sameDiagram` (see the search section).
- `checkTheorem` (`src/kernel/proof/theorem.ts`) replays a recorded
  derivation and is the provability certificate for family B.

## Family registry (`src/generate/index.ts`)

```ts
type KnobSpec = { id: string; label: string; min: number; default: number }
type GeneratedProblem = {
  diagram: Diagram          // becomes the edit diagram
  statement: string         // formula source text, shown to the user
  walkUpperBound?: number   // family B only: recorded action count
}
type GeneratorFamily = {
  id: string; label: string; description: string
  knobs: readonly KnobSpec[]
  generate(params: Record<string, number>, rng: () => number): GeneratedProblem
}
```

The registry exports the ordered family list:

- `prop-shrink` — "Random tautology (shrunk)"
- `prop-walk` — "Random tautology (rule walk)"

Knobs are free-form number inputs with defaults — no maxima. `min` exists
only for validity lower bounds (values below it are meaningless, not merely
inadvisable); cost at large values is governed by the attempt-cap and
search-fuel knobs, never by clamping inputs.

All randomness flows through the injected `rng: () => number`; generators are
deterministic given a seed. The UI seeds from `crypto.getRandomValues`; tests
use fixed seeds.

## Family A: generate-and-shrink (`src/generate/prop/`)

**Prop AST.** `atom(i) | top | bot | not(φ) | and(φ, ψ)`. No spans, no kernel
imports. ⊤/⊥ exist only during shrinking and never appear in output.
Alongside: a truth-table evaluator (all 2^n assignments) and a printer to
formula source text in `parseFormula`'s grammar (emits ¬ and ∧ only).

**Sampler.** Uniformly random formula tree with exactly the requested
connective count: root connective uniform over {not, and}, size budget split
uniformly between children of `and`, leaves uniform over the atom set. The
sampler is deliberately unbiased; the shrinker does the quality work.

**Shrinker.** Repeat until fixpoint:

1. Enumerate subformula occurrences with polarity. Polarity flips under
   `not`; with only {¬, ∧} every occurrence has a definite polarity.
2. Weakening substitution: positive occurrence → ⊥, negative → ⊤.
3. If the substituted formula is still a tautology, the occurrence was dead
   weight: apply the substitution, simplify constants away
   (⊤∧φ≡φ, ⊥∧φ≡⊥, ¬⊤≡⊥, ¬⊥≡⊤), restart the scan.

The fixpoint is a minimal tautology: every remaining occurrence's weakening
is falsifiable. The both-polarities-per-atom prefilter from the source notes
is intentionally omitted — at puzzle sizes the full check is already
instant, so the prefilter buys nothing.

**Accept/reject loop.** Knobs: atom count (min 1, default 3), sample size in
connectives (min 1, default 12 — the size formulas are sampled at, before
shrinking), minimum core size in connectives (min 1, default 6), and attempt
cap (min 1, default 10,000). Sample at the sample size → reject
non-tautologies → shrink → accept if the core meets the minimum size, else
resample. The sample size must be its own knob because the shrinker only
removes: cores can never exceed the sampled size, so sampling at the minimum
core size would degenerate into pure rejection sampling. Exceeding the
attempt cap throws with a clear message rather than spinning on an
unsatisfiable knob combination.

**Output.** The core prints as `∀P Q R:o. <formula>`, quantifying exactly the
atoms that survived shrinking, and runs through the existing
`formulaToDiagram`. The source text is returned as `statement`.

## Family B: kernel forward walk (`src/generate/walk/`)

**Harness.** `PrimitiveStepRecorder` over `EMPTY_PROOF_CONTEXT` (no
definitions or theorem citations), starting from the blank sheet with empty
boundary, forward orientation. Every move is a recorded `ProofStep`; at the
end `checkTheorem` validates the full derivation, certifying provability by
construction in the real move system.

**Prelude.** Recorded steps build the `∀P Q…:o` shell: an empty
`doubleCutIntro` at the root, then vacuity-inserted bare wires of sig
`relSig([])` scoped to the annulus — matching the shape
`quantifierScope('forall')` produces, so family B statements have the same
shape as family A's. The walk then operates in the inner body region and
below.

**Move alphabet** (forward-legal, propositional fragment only):

- `doubleCutIntro` — empty, or wrapping an existing atomic selection
- `doubleCutElim` — where the annulus is empty
- `atomSpawn` of a quantified proposition wire — negative regions (gate-enforced)
- `iteration` of an atomic selection (single atom or single cut-subtree) into
  a deeper region
- `deiteration` via `findDeiterationEvidence`
- `erasure` of an atomic selection — positive regions

No identity/wire-surgery/arity rules — not part of the propositional
fragment. "Atomic selection" means a single atom node or a single cut with
its entire subtree.

**Bias.** In the forward direction `atomSpawn` is the junk source (it is
insertion, seen from the user's backward proof). Move weights favor
iteration, deiteration, and double-cut moves over spawn and erasure. Weights
are explicit named constants on the family definition and are **per class**:
a move class with at least one applicable candidate participates with its
class weight, then a candidate is drawn uniformly within the chosen class.
(Summing weight per candidate instead was measured to let the
combinatorially-growing double-cut/iteration candidate counts drown spawn
entirely.) Weights shape the sampling distribution only — legality always
comes from enumerating actually-applicable moves, and correctness never
depends on the weights.

**Cleanup and filters.** After the walk, ∀-wires with no surviving atom
occurrences (bare wires — all endpoints are pins) are removed by recorded
forward vacuity-delete steps, so the atoms knob is an upper bound and the
derivation still certifies the cleaned diagram. (Rejecting walks with
unused wires instead was measured to make multi-atom generation practically
never succeed.) Then a prop-fragment diagram→formula reader (cuts→¬,
juxtaposition→∧, atom nodes→atoms) converts the result back to a formula.
This serves two purposes: the UI gets a readable `statement` for family B,
and the family A minimality check runs on it — outputs whose weakening test
finds dead weight are rejected and the walk reruns with the same knobs;
exceeding the attempt cap throws with a clear message.

**Knobs.** Atoms (max) — the number of ∀ wires the prelude declares, an
upper bound on the atoms of the resulting theorem (min 1, default 2); walk
length (moves after the prelude; min 1, default 12); attempt cap (min 1,
default 1,000). Walk length is an upper bound on difficulty, not a
guarantee; the honest number comes from the search.

## Minimal-proof search (`src/generate/search/`)

**Direction and goal.** Backward-oriented — exactly what the user plays.
Start at the generated theorem diagram, apply steps with
`applyStep(…, 'backward')` over `EMPTY_PROOF_CONTEXT`; the goal is the blank
sheet (dismantling the ∀ shell included), tested literally: exactly one
region (the root sheet), zero nodes, zero wires. No isomorphism machinery is
needed for the goal test.

**Enumerator.** New work. For a diagram it emits every applicable atomic
move in the backward propositional alphabet — the mirror of the walk's:

- `erasure` of an atomic selection — negative regions (backward gate)
- `atomSpawn` — positive regions
- `doubleCutElim` (empty annulus); `doubleCutIntro` (empty, or around one
  atomic selection, per region)
- `iteration` (atomic selection × legal deeper target); `deiteration` via
  `findDeiterationEvidence`
- `vacuity` bare-wire insert/delete — needed to remove the ∀ wires at the end

All finitely enumerable. Selection construction reuses the pure helpers in
`src/app/interact/moves.ts` (`erasureStep` auto-includes orphaned rider
wires, `deiterationStep`) rather than reimplementing them; the import is
acyclic at file level.

**Auto-pin bundling.** Deleting a quantified wire's last atom occurrence
would strand the wire below the kernel's two-end floor
(`ScopePreservationError`); the app's erase gesture resolves this by
inserting a pin step within the same action, and the search models the same
gesture: an erasure/deiteration candidate that raises the error gets the
recorder-style pin step applied first and is retried, with pin + delete
counted as **one move** (both steps appear in the reported step trail).
Without this, no deletion-only proof can ever reach the blank sheet — the
declaration pin is otherwise unremovable.

**Algorithm: two phases.** The insertion-flavored moves (`atomSpawn`,
`doubleCutIntro`, iteration-copy, vacuity-insert) give the full alphabet a
branching factor of roughly 30 even on the smallest theorem, so exhaustively
proving "no shorter proof exists" over the full alphabet is infeasible
(≈ 30^d states to close depth d). The search therefore runs in two phases:

- **Phase 1 — deletion-only, complete.** Alphabet: `erasure` (negative),
  `deiteration`, `doubleCutElim`, vacuity bare-wire delete. Every one of
  these strictly shrinks the diagram (regions + nodes + wires), so the
  reachable state space is finite and small. A breadth-first search with
  isomorphism deduplication explores it **completely** — no fuel needed. If
  the blank sheet is reached, the minimal deletion-only proof length is
  exact; if the whole space is exhausted without reaching it, the problem
  **provably requires insertion** — the notes' strongest difficulty signal,
  established as a theorem rather than a fuel-limited guess.
- **Phase 2 — full alphabet, fuel-bounded.** Runs only when phase 1 proves
  insertion is required. Iterative-deepening DFS over the full alphabet
  under an explicit expanded-state fuel budget, reporting a solve or the
  deepest fully-exhausted depth as an honest bound.

Deterministic; no RNG. Memoization/deduplication in both phases: states are
bucketed by an iso-invariant digest (multisets of region depths, node kinds
per depth, wire signatures with endpoint counts — all preserved by diagram
isomorphism); within a bucket, identity is confirmed by `sameDiagram`
against stored representatives, so pruning is exact, never hash-optimistic.
In phase 2 a state is pruned when an isomorphic state was already visited
with at least as much remaining depth budget.

The reported length is minimal **within the phase that produced it**
(deletion-only alphabet for phase 1, full atomic alphabet for phase 2), and
the label says which. A phase-1 length is an upper bound on the full-system
minimum; the alternative — closing the full alphabet exhaustively — is the
infeasible computation above.

**Outputs, honestly labeled.**

- Phase 1 solves at depth k → **minimal deletion-only proof length = k**
  (labeled as such — an upper bound on the full-system minimum), plus the
  proven fact that insertion is NOT required.
- Phase 1 proves unsolvable → **"requires insertion"**, proven. If phase 2
  then solves at depth k with all shallower depths fully exhausted →
  **minimal proof length = k** over the full atomic alphabet.
- **"Requires rule class C"** is computed by definition, not inspection:
  rerun the solving phase at the found depth with class C removed; if no
  proof exists, every minimal proof uses C. Classes checked: insertion
  (`atomSpawn`; free — it is phase 1's verdict), iteration/deiteration,
  double-cut. In phase 2 a probe that exhausts its fuel leaves the
  requirement unproven and it is omitted — `requires` only ever lists
  proven requirements.
- Phase 2 fuel exhausted → report only the bound actually established ("no
  proof within d moves" for the deepest fully-exhausted depth d) together
  with the proven "requires insertion", plus `walkUpperBound` when the
  problem came from family B. Never a fabricated number.

The search returns a plain result object; the UI renders it as the
difficulty line.

## UI (`src/app/generate-entry.ts` + shell wiring)

The panel mirrors `formula-entry.ts` in lifecycle (`open/close/deactivate/
dispose`, dialog role, Escape handling, `output role=alert` error surface).

Contents:

- Family selector over the registry.
- Knob number-inputs rendered from the selected family's `KnobSpec`s.
- Search-fuel input (expanded-state cap). The default is sized in tests so
  default-knob problems complete within it.
- **Generate** — seeds an RNG from `crypto.getRandomValues`, runs the family,
  then the search; displays the statement and the difficulty line. Pressing
  Generate again regenerates in place.
- **Create diagram** — hands `diagram` to the same commit callback the
  formula entry uses (replaces the edit diagram; `src/app/shell.ts` formula
  entry commit path).
- **Cancel.**

Shell: one new `Random…` button beside `Formula…`, hidden outside edit mode
and deactivated on mode change — identical treatment to `formulaBtn`.

Generation + search run synchronously at puzzle sizes under the fuel cap. If
a real problem size blocks noticeably, the search moves to a worker (the
`optimize-worker` pattern exists); not built speculatively.

## Testing (`tests/generate/`, `tests/app/`, `e2e/`)

Tests land as each piece is built. All generator tests use fixed seeds.

- **Prop core.** Evaluator vs hand-computed truth tables; sampler emits
  exactly the requested connective count and only {¬, ∧}; printer →
  `parseFormula` round-trips to the same tree; shrinker takes hand-built junk
  tautologies (e.g. ¬(P∧¬P) conjoined with dead weight) to their known
  cores; property test over many seeds: every shrinker output is a tautology
  whose every weakening is falsifiable.
- **Family A.** Over a seed batch: output parses, meets the size knob, is
  minimal, `formulaToDiagram` accepts it; attempt cap throws loudly on an
  impossible knob combination.
- **Family B.** Over a seed batch: `checkTheorem` passes on the emitted
  theorem; cross-check — `sameDiagram` holds between the walk's diagram and
  `formulaToDiagram(statement)`, pinning the reader and the prelude shape
  against the formula pipeline in one assertion; minimality filter verified
  by feeding the reader's formula back through the weakening test.
- **Enumerator.** Soundness: every emitted candidate applies via
  `applyStep(…, 'backward')` without error, over a corpus of generated
  diagrams. Completeness spot-checks: hand-built positions where a specific
  move (a deiteration, an empty-annulus elim) must be offered.
- **Search.** Tiny theorems with hand-computed minimal lengths verified
  exactly — e.g. ∀P:o. ¬(P∧¬P) has the 5-step deletion-only backward proof
  (deiterate inner P, erase outer P, double-cut-elim the body pair,
  vacuity-delete the bare wire, double-cut-elim the shell) and its inner
  cut can only be emptied by deiteration, so phase 1 must report length 5
  requiring the iteration class, insertion proven unnecessary. Peirce's law
  in ¬/∧ form (∀P Q:o. ¬(¬(¬(P∧¬Q)∧¬P)∧¬P)) is the classic
  insertion-requiring case: phase 1 must prove it unsolvable and phase 2
  takes over, returning a solve or an honest fuel bound. Integration
  property: for default knobs, both families' outputs run through the
  search without error, returning either a solve or an honest bound —
  exact-solve assertions are reserved for small hand-chosen cases that
  finish inside the ordinary suite's 5-second test timeout. Default phase-2
  fuel is sized so a default-knob run returns promptly with at worst an
  honest bound.
- **UI.** `tests/app/` unit tests mirroring the formula-entry tests
  (open/close/escape, knob rendering per family, error surfacing); one
  Playwright spec in `e2e/`: open Random…, generate, create diagram, enter
  Prove backward, confirm the track starts on the generated diagram.
