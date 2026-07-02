# Plan 11e: Relation Fold/Unfold (definition-node parity)

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Relation definitions become first-class, on par with term constants (user requirement: "part of the point of this exercise was to demonstrate relational and term definitions"). A named relation like ℕ can appear in a diagram as a single labeled reference node; fold/unfold rules convert between the reference and the inlined body as definitional equivalences. Theorem statements then ship with *folded* guards — `ℕ(a) ∧ ℕ(b) ⟹ …` becomes literally the stored diagram — while derivations unfold only their working copies.

**Architecture:** Branch `plan-11-arithmetic` (continues). New node kind `{ kind: 'ref'; region; defId; arity }` parallel to atoms (arg ports 0..arity−1, no output, no binder). `ProofContext` gains `relations`. Two rules: `relUnfold` (splice the body onto the reference's arg wires) and `relFold` (extraction-fingerprint check against the body, mirroring comprehension abstraction's occurrence check). Both definitional equivalences — polarity-blind.

**Prerequisite finding (survey, 2026-07-02): `node.kind` has no exhaustive switch anywhere in the codebase** — every dispatch is an if/else or a `n.kind === 'term' ? … : …` ternary whose else assumes atom. Adding a third kind produces zero compile errors and fails silently: the matcher's `nodeCompatible` special-cases only atom&&atom so ref-ref pairs would fall through to `termVerdict` and never match; seven rebuild ternaries (json.ts:17, extract.ts:98, splice.ts:128, edit.ts:48, vacuous.ts:71, doublecut.ts:80, comprehension.ts:107/:215) would silently rewrite a ref into an atom; `nodeContentKey` would key refs as `'atom'` — defId-blind, so references to DIFFERENT relations would get equal canonical forms (a soundness bug in anything using fingerprints). Hence Task 0.

**Design decisions (settled):**
- Arity is stored INLINE on the ref node. `mkDiagram` is context-free by design and validates ports against the stored arity; defId resolution (exists? arity agrees?) is checked where context exists: the rules and `verifyTheory`/`loadTheory`.
- Matcher: ref matches ref by `defId` and `arity` equality (region-independent, like constants), plus the ordinary arg-wire image alignment. Kind mismatch never matches.
- Canonical content key: `ref:${defId}:${arity}`, no binder color, port order `a0..a{arity-1}`.
- Relation bodies are closed by construction: a `DiagramWithBoundary` is a self-contained diagram, so every bubble in a body is content with ∃-meaning (e.g. `R(x) := ∃S[S(x)]` is fine). *Corrected in Task 2b (the original "no external binder stubs — refuse at verification" premise was wrong): openness is NOT a property of a stored body — it exists only as the splice-time binder map, and relUnfold always splices with an EMPTY map, so copying any stored bubble is unconditionally sound. No self-containedness refusal exists; open-pattern DEFINITION authoring (a UI/parameter mechanism) remains deferred.*
- View: refs render via `atomGeometry(arity)` with the defId as the glyph label (the same labeled-lens treatment constants get). No new interaction surface in this plan (placing refs from the UI belongs to the relation-naming feature).

---

### Task 0: Exhaustive node-kind dispatch (behavior-preserving hardening)

**Files:** every site in the survey list — diagram.ts (requiredPorts :54-66, validation :202-214, canonicalizeFreePorts :90), json.ts (:17, :88-100), canonical/canonical.ts (:115-131, :142-150), subgraph/match.ts (:43-49, :213, :230-240), subgraph/extract.ts (:41, :98), subgraph/splice.ts (:128-131), rules/access.ts (:9), rules/vacuous.ts (:36, :53-56, :71), rules/doublecut.ts (:35, :80), rules/comprehension.ts (:84, :107, :215), app/edit.ts (:48), app/actions.ts (:38, :55), app/shell.ts (:103, :114), app/session.ts (:151), theories/macros.ts (:85-118 filters), view/scene.ts (:53-55). (Line numbers are survey-time anchors; find the sites by shape.)

Convert each `node.kind` if/else or ternary into an exhaustive `switch (n.kind)` (or explicit `=== 'atom'` guards where a filter is genuinely kind-specific) such that adding a member to the `DiagramNode` union produces a COMPILE ERROR at every site that must decide. Use the standard `never`-exhaustion idiom consistent with how the codebase handles other unions (check step.ts's applyStep — no default, TS exhaustiveness via return type). Fix `termNodeAt`'s error message to name the actual kind rather than hardcoding "is an atom". ZERO behavior change: the full suite must pass untouched (no test edits in this task; if a test fails, the conversion changed behavior — fix the conversion).

- [x] Full suite green with no test-file changes; tsc clean. Commit `plan 11e task 0: exhaustive node-kind dispatch (hardening)`.

### Task 1: The ref node kind through the kernel core

**Files:** diagram.ts (union member + requiredPorts + validation: arity ≥ 0 integer, ports validated against it), json.ts (ser/parse `{kind:'ref',region,defId,arity}`, strict keys), canonical/canonical.ts (content key + port order, no binder read), subgraph/match.ts (ref-branch in nodeCompatible: defId + arity equality; posKey arg handling), extract/splice (refs rebuild as-is: region remapped, defId/arity copied, never bound-outside), builder.ts (`ref(region, defId, arity): NodeId`), edit.ts rebuild case.
**Test:** `tests/kernel/diagram/ref-node.test.ts` (new) + additions to match/extract/splice/json/canonical suites.

Compiler-driven: after Task 0, adding the union member enumerates every decision site. Tests first, minimum: construction + requiredPorts (arity ports, no output); mkDiagram rejects a ref with a port index ≥ arity and an endpoint on a nonexistent arg; JSON roundtrip + strict keys; canonical: two refs same defId/arity/wiring → equal fingerprints; different defIds, same shape otherwise → DIFFERENT fingerprints (the survey's soundness case, pinned); matcher: ref-ref same defId matches with aligned arg wires; different defId refuses; ref never matches atom or term; iteration/deiteration of a subgraph containing a ref round-trips; extract/splice preserve defId/arity.

- [x] Failing tests observed → implement → pass; full suite + tsc green. Commit `plan 11e task 1: relation reference node kind`.

### Task 2: relations in ProofContext; relUnfold/relFold rules

**Files:** proof/step.ts (`ProofContext` gains `readonly relations: ReadonlyMap<string, DiagramWithBoundary>`; step variants `{rule:'relUnfold'; node: NodeId}` and `{rule:'relFold'; sel: SubgraphSelection; defId: string; args: readonly WireId[]}` + dispatch), the 7 src construction sites (boot.ts:45, lambda.ts:25, store.ts:37/:40, session.ts:254, frege.ts:369/:372) and ~26 test files gain the field, rules/reldef.ts (new), proof/json.ts + compose.ts wiring, store.ts `verifyTheory` extended: every ref node in any theorem side or relation body resolves (defId present, arity equals boundary length). *(Task 2b: the originally-planned "relation body self-contained / no external binder stubs — refuse loudly" check was REMOVED. Stored bodies are closed by construction; openness exists only as the splice-time binder map, which relUnfold always leaves empty, so a top-level bubble like `∃S[S(x)]` is legitimate content. Only defId-resolution + arity remain.)*
**Test:** `tests/kernel/rules/reldef.test.ts` + store/json/compose entries.

`applyRelUnfold(d, node, relations)`: node is a ref (kind-checked, loud); defId resolves; def boundary length === node arity (refuse naming both); splice the body into the node's region with the boundary onto the node's arg wires (existing splice path, like insertion); remove the ref node. `applyRelFold(d, sel, defId, args, relations)`: mirror comprehension abstraction's occurrence check — extractSubgraph the selection, binderStubs must be empty, args a distinct permutation of the attachments, reordered boundary fingerprint must equal the def's; replace the selection with a ref node on args. Soundness comment on both: definitional equivalence (the reference is notation for its body), hence polarity-blind; fold's fingerprint check is what keeps it exact.

Tests, minimum: unfold ℕ-shaped ref → body lands attached to the arg wire, ref gone; fold it back → fingerprint equals the original ref diagram (round-trip); unfold refuses unknown defId / arity mismatch; fold refuses a near-miss body (one node changed — fingerprint mismatch observed); both work inside a cut (polarity-blind); replay + json + compose entries; verifyTheory ACCEPTS a relation body with a top-level bubble (`∃S[S(x)]`-shaped, closed by construction) and relUnfold copies that bubble as fresh content; verifyTheory refuses a theorem that uses an unresolvable ref (unknown defId / arity mismatch).

- [x] Failing tests observed → implement → pass; full suite + tsc green. Commit `plan 11e task 2: relations in ProofContext; relUnfold/relFold`.

### Task 3: View + app gates

**Files:** view/scene.ts (ref → `atomGeometry(arity)`), view/display.ts (defId label on ref nodes — same visual voice as constant glyphs), app gates (actions/session/shell/hittest: refs are neither convertible terms nor bubble-bound atoms — the Task 0 switches already forced explicit decisions; verify each is the RIGHT decision and test the visible ones), e2e sanity (boot unchanged — no bundled refs yet).
**Test:** view test additions + app gate tests.

- [x] Failing tests observed → implement → pass; full suite + `npm run e2e` green. Commit `plan 11e task 3: ref rendering and app gates`.

### Task 4: Folded-guard integration proof

**Files:** `tests/kernel/proof/folded-guard.test.ts` (new; test-only).

The de-risk for the theorem plan: a ProofContext carrying a small relation (a two-node closed body, arity 1), a theorem whose lhs contains a folded ref-guard on a boundary line; the derivation iterates the ref, relUnfolds the COPY, does one real rule application inside the unfolded material, and the rhs keeps the AMBIENT guard folded. checkTheorem green; assert the rhs still contains the ref node (fold survived the derivation) and the statement fingerprints are ref-keyed (unfold-everything would NOT be iso). This is the exact usage pattern the arithmetic theorems will follow.

- [x] Test written (failing only until wired correctly), observed green; full suite green. Commit `plan 11e task 4: folded-guard integration proof`.

### Task 5: Adversarial review

Mutation probes (each observed fail → revert → pass): (1) matcher ref-branch compares arity only (drop defId) — the different-defId fingerprint/match tests must fail; (2) one rebuild site coerces ref→atom (reintroduce the survey's ternary at splice.ts) — round-trip/derivation tests must fail; (3) canonical content key drops defId — the soundness pin must fail; (4) relFold skips the fingerprint check — the near-miss refusal must fail; (5) relUnfold splices without removing the ref — an equivalence test must fail. Independent hunt: fold/unfold under open-pattern hosts; refs inside comprehension bodies and insertion patterns (patterns are self-contained namespaces — do refs resolve at APPLICATION time? verify the rule resolves against ctx at replay, and a stored pattern containing a ref round-trips); canonicalizeFreePorts skips refs; deiteration of ref-containing copies. Plan-doc sync + verdict.

- [x] APPROVED verdict recorded; plan-doc sync. Commit.

---

**Deferred (recorded):** open-pattern relation definitions; placing refs from the UI (relation-naming feature); restating bundled theorems with folded guards (Plan 11 final, next).

---

## Task 5 execution record (adversarial review, 2026-07-02)

Independent reviewer; wrote none of the reviewed code (commits cfec2ad, 0681a32,
f0cf334, fdfdcf5, 7a50bb2, facb25f). Baseline before probing: vitest 663/663,
tsc clean, e2e 3/3.

### Part A — mandated mutation probes

Each: mutate one src line → run targeted tests → observe ≥1 fail → `git checkout`
revert → observe pass. `git diff src/` empty after all five.

| # | Mutation | Catching test (observed FAIL) |
|---|----------|-------------------------------|
| 1 | matcher ref-branch drops `defId` (compares arity only), `match.ts:257` | `ref-node.test.ts › ref node — matcher › ref does not match a ref of a different defId` |
| 2 | splice rebuild coerces `ref`→`atom` (pre-Task-0 ternary shape), `splice.ts:130` | `ref-node.test.ts › iteration round-trip › iterates a ref-containing subgraph into a cut and deiterates it back` (+ `extract/splice preserve defId and arity`) |
| 3 | canonical content key drops `defId` (`ref:${arity}`), `canonical.ts:137` | `ref-node.test.ts › canonical fingerprint (soundness pin) › two refs identical except defId have DIFFERENT fingerprints` |
| 4 | relFold skips the boundary-fingerprint check, `reldef.ts:85` | `reldef.test.ts › relFold — refuses a near-miss body › refuses to fold a D-body as the C-relation` |
| 5 | relUnfold splices without removing the ref, `reldef.ts:49` | `reldef.test.ts › relUnfold — inlines the body onto arg-0 and drops the reference` (+ 5 more: fold round-trip, polarity-blind, replay, ∃-body, folded-guard) |

All five probes are caught. Every mutation reverted; no defects surfaced by Part A.

### Part B — independent soundness hunt

New tests committed in `tests/kernel/rules/reldef-review.test.ts` (4 tests, all
green; each verified discriminating — test 2 in particular fails under Probe 3's
key mutation, so it is not vacuous).

- **Task 2b correction (sharpest case).** relUnfold calls `spliceSubgraph` with an
  EMPTY binder map, and splice's `rebuildNode` copies every body region/node
  verbatim (a bubble becomes a fresh child region of the splice region, its atoms
  rebound to that copied region — never to any host binder, because the empty map
  contributes nothing to `binderMap`). Consider the adversarial body authored to
  *look* like an `extractSubgraph` of an open pattern: a top-level bubble binding
  an atom whose arg is the boundary — structurally the exact shape an external
  binder stub has. If that bubble had been *intended* as an open parameter, that
  intent is nowhere in the stored `DiagramWithBoundary`: a stored body carries no
  binder map, so there is no "stub" bit to read. Unfolding therefore copies the
  bubble as a genuine ∃ over fresh content. The outcome is a well-formed diagram
  (splice re-runs `mkDiagram`, which would throw on any dangling binder) in which
  the atom is bound by the copied bubble and cannot escape. So the only thing
  "lost" is an open reading the author never stored; what is produced is a sound,
  fully-closed statement (∃-closure), merely weaker than the imagined-open intent.
  No forgery is possible — the atom cannot end up bound outside its copied bubble.
  Test: `Task 2b soundness — a stored top-level bubble unfolds to valid ∃-content`.

- **relFold as an introduction rule; forgery via a fingerprint-equal body.** Two
  relations R1, R2 with byte-identical bodies but different defIds. Folding names
  its target explicitly (`applyRelFold(..., defId, ...)`) and stamps that defId
  into the emitted `{kind:'ref'; defId; …}`. The two resulting refs are DISTINCT
  diagrams: the canonical content key is `ref:${defId}:${arity}` (defId, not body)
  and the matcher compares defId + arity (match.ts:257) — no code path anywhere
  canonicalizes or matches a ref by its body. Grep confirms the only `ref:`
  producer is canonical.ts:137 and the only consumers are string comparisons; no
  reverse parse exists. The derivation `R1(a) → unfold → fold-as-R2 → R2(a)` is a
  valid, sound rewrite precisely because identical bodies denote the same relation
  (R1(a) ⟺ R2(a) is itself a definitional equivalence); it forges nothing, and it
  cannot be turned against relations with *different* bodies because fold's
  fingerprint check (Probe 4) blocks any body that is not isomorphic to R2's.
  Test: `fold is defId-directed — no ref is canonicalized by its body`.

- **Canonical key injectivity (digit-only arity).** The key is a whole-string
  comparison, never parsed, so injectivity of (defId, arity) → key reduces to
  string equality; because arity always renders as a non-empty digit run, the last
  colon is an unambiguous separator and no distinct pair can collide. The
  adversarial `a:1` (arity 1, key `ref:a:1:1`) vs `a` (arity 1, key `ref:a:1`) —
  the pair a naive last-colon split could blur — get different fingerprints, as do
  `a:1`/`a:2` and `a`/`b`. Test: `canonical key injectivity — adversarial
  colon-bearing defIds`.

- **relFold args discipline (diagonal).** With a genuine arity-2 occurrence
  (distinct attachments w0, w1), the honest fold `[w0, w1]` is accepted while the
  diagonal `[w0, w0]` is refused by the distinctness gate (`new Set(args).size !==
  args.length`) before any fingerprint work — so a host wire cannot be collapsed
  into two argument positions. Test: `relFold args discipline — the diagonal is
  refused`.

- **Refs in insertion / comprehension patterns (self-contained namespaces).**
  `spliceSubgraph.rebuildNode` copies a ref verbatim (defId/arity preserved —
  Probe 2 pins this), so a pattern-embedded ref splices with its defId intact.
  Resolution is deferred to application/verification: `applyRelUnfold` /
  `applyRelFold` read `ctx.relations`, and `verifyTheory.assertRefsResolve`
  requires every ref in a theorem side or relation body to resolve. Inserting a
  ref to an as-yet-unknown relation into a negative region is itself sound (it is
  a fresh predicate symbol / weakening); it simply cannot be unfolded and would be
  caught by `assertRefsResolve` if it survived into a stored theorem side.
  `ref-node.test.ts`'s iteration/deiteration round-trip already covers a
  ref-containing subgraph copied across regions.

- **App exposure.** The relFold pending flow (`shell.ts:604-608`) commits via
  `applyF → applyForward → applyStep(step, ctx) → applyRelFold(d, sel, defId,
  args, ctx.relations)`. Every app relFold therefore passes the kernel
  fingerprint gate against `ctx.relations`; there is no diagram-mutating path that
  constructs a fold outside `applyStep`.

- **checkTheorem with folded guards (boundary discipline).** Task 4's
  `folded-guard.test.ts` replays a derivation whose lhs boundary line's only
  consumer is a ref node, iterates the ref, unfolds only the copy, applies a real
  rule, and keeps the ambient guard folded; `checkTheorem` is green, the rhs still
  carries the ref, and unfold-everything is NOT iso to the folded rhs
  (ref-keyed statement identity). The per-step boundary-survival checks hold with
  a ref as the boundary consumer.

### Result

Defects found: none. No source change was required; `git diff src/` is empty
(all five probes reverted). Final counts: **vitest 667/667** (663 + 4 review
additions), **tsc clean**, **e2e 3/3**.

**Verdict: APPROVED.**
