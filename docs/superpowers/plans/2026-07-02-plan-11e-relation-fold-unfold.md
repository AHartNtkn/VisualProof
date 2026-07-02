# Plan 11e: Relation Fold/Unfold (definition-node parity)

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Relation definitions become first-class, on par with term constants (user requirement: "part of the point of this exercise was to demonstrate relational and term definitions"). A named relation like ℕ can appear in a diagram as a single labeled reference node; fold/unfold rules convert between the reference and the inlined body as definitional equivalences. Theorem statements then ship with *folded* guards — `ℕ(a) ∧ ℕ(b) ⟹ …` becomes literally the stored diagram — while derivations unfold only their working copies.

**Architecture:** Branch `plan-11-arithmetic` (continues). New node kind `{ kind: 'ref'; region; defId; arity }` parallel to atoms (arg ports 0..arity−1, no output, no binder). `ProofContext` gains `relations`. Two rules: `relUnfold` (splice the body onto the reference's arg wires) and `relFold` (extraction-fingerprint check against the body, mirroring comprehension abstraction's occurrence check). Both definitional equivalences — polarity-blind.

**Prerequisite finding (survey, 2026-07-02): `node.kind` has no exhaustive switch anywhere in the codebase** — every dispatch is an if/else or a `n.kind === 'term' ? … : …` ternary whose else assumes atom. Adding a third kind produces zero compile errors and fails silently: the matcher's `nodeCompatible` special-cases only atom&&atom so ref-ref pairs would fall through to `termVerdict` and never match; seven rebuild ternaries (json.ts:17, extract.ts:98, splice.ts:128, edit.ts:48, vacuous.ts:71, doublecut.ts:80, comprehension.ts:107/:215) would silently rewrite a ref into an atom; `nodeContentKey` would key refs as `'atom'` — defId-blind, so references to DIFFERENT relations would get equal canonical forms (a soundness bug in anything using fingerprints). Hence Task 0.

**Design decisions (settled):**
- Arity is stored INLINE on the ref node. `mkDiagram` is context-free by design and validates ports against the stored arity; defId resolution (exists? arity agrees?) is checked where context exists: the rules and `verifyTheory`/`loadTheory`.
- Matcher: ref matches ref by `defId` and `arity` equality (region-independent, like constants), plus the ordinary arg-wire image alignment. Kind mismatch never matches.
- Canonical content key: `ref:${defId}:${arity}`, no binder color, port order `a0..a{arity-1}`.
- Relation bodies (v1): self-contained `DiagramWithBoundary` — no external binder stubs (open-pattern relation definitions refuse loudly at verification; deferred).
- View: refs render via `atomGeometry(arity)` with the defId as the glyph label (the same labeled-lens treatment constants get). No new interaction surface in this plan (placing refs from the UI belongs to the relation-naming feature).

---

### Task 0: Exhaustive node-kind dispatch (behavior-preserving hardening)

**Files:** every site in the survey list — diagram.ts (requiredPorts :54-66, validation :202-214, canonicalizeFreePorts :90), json.ts (:17, :88-100), canonical/canonical.ts (:115-131, :142-150), subgraph/match.ts (:43-49, :213, :230-240), subgraph/extract.ts (:41, :98), subgraph/splice.ts (:128-131), rules/access.ts (:9), rules/vacuous.ts (:36, :53-56, :71), rules/doublecut.ts (:35, :80), rules/comprehension.ts (:84, :107, :215), app/edit.ts (:48), app/actions.ts (:38, :55), app/shell.ts (:103, :114), app/session.ts (:151), theories/macros.ts (:85-118 filters), view/scene.ts (:53-55). (Line numbers are survey-time anchors; find the sites by shape.)

Convert each `node.kind` if/else or ternary into an exhaustive `switch (n.kind)` (or explicit `=== 'atom'` guards where a filter is genuinely kind-specific) such that adding a member to the `DiagramNode` union produces a COMPILE ERROR at every site that must decide. Use the standard `never`-exhaustion idiom consistent with how the codebase handles other unions (check step.ts's applyStep — no default, TS exhaustiveness via return type). Fix `termNodeAt`'s error message to name the actual kind rather than hardcoding "is an atom". ZERO behavior change: the full suite must pass untouched (no test edits in this task; if a test fails, the conversion changed behavior — fix the conversion).

- [ ] Full suite green with no test-file changes; tsc clean. Commit `plan 11e task 0: exhaustive node-kind dispatch (hardening)`.

### Task 1: The ref node kind through the kernel core

**Files:** diagram.ts (union member + requiredPorts + validation: arity ≥ 0 integer, ports validated against it), json.ts (ser/parse `{kind:'ref',region,defId,arity}`, strict keys), canonical/canonical.ts (content key + port order, no binder read), subgraph/match.ts (ref-branch in nodeCompatible: defId + arity equality; posKey arg handling), extract/splice (refs rebuild as-is: region remapped, defId/arity copied, never bound-outside), builder.ts (`ref(region, defId, arity): NodeId`), edit.ts rebuild case.
**Test:** `tests/kernel/diagram/ref-node.test.ts` (new) + additions to match/extract/splice/json/canonical suites.

Compiler-driven: after Task 0, adding the union member enumerates every decision site. Tests first, minimum: construction + requiredPorts (arity ports, no output); mkDiagram rejects a ref with a port index ≥ arity and an endpoint on a nonexistent arg; JSON roundtrip + strict keys; canonical: two refs same defId/arity/wiring → equal fingerprints; different defIds, same shape otherwise → DIFFERENT fingerprints (the survey's soundness case, pinned); matcher: ref-ref same defId matches with aligned arg wires; different defId refuses; ref never matches atom or term; iteration/deiteration of a subgraph containing a ref round-trips; extract/splice preserve defId/arity.

- [ ] Failing tests observed → implement → pass; full suite + tsc green. Commit `plan 11e task 1: relation reference node kind`.

### Task 2: relations in ProofContext; relUnfold/relFold rules

**Files:** proof/step.ts (`ProofContext` gains `readonly relations: ReadonlyMap<string, DiagramWithBoundary>`; step variants `{rule:'relUnfold'; node: NodeId}` and `{rule:'relFold'; sel: SubgraphSelection; defId: string; args: readonly WireId[]}` + dispatch), the 7 src construction sites (boot.ts:45, lambda.ts:25, store.ts:37/:40, session.ts:254, frege.ts:369/:372) and ~26 test files gain the field, rules/reldef.ts (new), proof/json.ts + compose.ts wiring, store.ts `verifyTheory` extended: every relation body is self-contained (no external binder stubs — refuse loudly) and every ref node in any theorem side or relation body resolves (defId present, arity equals boundary length).
**Test:** `tests/kernel/rules/reldef.test.ts` + store/json/compose entries.

`applyRelUnfold(d, node, relations)`: node is a ref (kind-checked, loud); defId resolves; def boundary length === node arity (refuse naming both); splice the body into the node's region with the boundary onto the node's arg wires (existing splice path, like insertion); remove the ref node. `applyRelFold(d, sel, defId, args, relations)`: mirror comprehension abstraction's occurrence check — extractSubgraph the selection, binderStubs must be empty, args a distinct permutation of the attachments, reordered boundary fingerprint must equal the def's; replace the selection with a ref node on args. Soundness comment on both: definitional equivalence (the reference is notation for its body), hence polarity-blind; fold's fingerprint check is what keeps it exact.

Tests, minimum: unfold ℕ-shaped ref → body lands attached to the arg wire, ref gone; fold it back → fingerprint equals the original ref diagram (round-trip); unfold refuses unknown defId / arity mismatch; fold refuses a near-miss body (one node changed — fingerprint mismatch observed); both work inside a cut (polarity-blind); replay + json + compose entries; verifyTheory refuses a theory whose relation body carries an external binder stub, and one whose theorem uses an unresolvable ref.

- [ ] Failing tests observed → implement → pass; full suite + tsc green. Commit `plan 11e task 2: relations in ProofContext; relUnfold/relFold`.

### Task 3: View + app gates

**Files:** view/scene.ts (ref → `atomGeometry(arity)`), view/display.ts (defId label on ref nodes — same visual voice as constant glyphs), app gates (actions/session/shell/hittest: refs are neither convertible terms nor bubble-bound atoms — the Task 0 switches already forced explicit decisions; verify each is the RIGHT decision and test the visible ones), e2e sanity (boot unchanged — no bundled refs yet).
**Test:** view test additions + app gate tests.

- [ ] Failing tests observed → implement → pass; full suite + `npm run e2e` green. Commit `plan 11e task 3: ref rendering and app gates`.

### Task 4: Folded-guard integration proof

**Files:** `tests/kernel/proof/folded-guard.test.ts` (new; test-only).

The de-risk for the theorem plan: a ProofContext carrying a small relation (a two-node closed body, arity 1), a theorem whose lhs contains a folded ref-guard on a boundary line; the derivation iterates the ref, relUnfolds the COPY, does one real rule application inside the unfolded material, and the rhs keeps the AMBIENT guard folded. checkTheorem green; assert the rhs still contains the ref node (fold survived the derivation) and the statement fingerprints are ref-keyed (unfold-everything would NOT be iso). This is the exact usage pattern the arithmetic theorems will follow.

- [ ] Test written (failing only until wired correctly), observed green; full suite green. Commit `plan 11e task 4: folded-guard integration proof`.

### Task 5: Adversarial review

Mutation probes (each observed fail → revert → pass): (1) matcher ref-branch compares arity only (drop defId) — the different-defId fingerprint/match tests must fail; (2) one rebuild site coerces ref→atom (reintroduce the survey's ternary at splice.ts) — round-trip/derivation tests must fail; (3) canonical content key drops defId — the soundness pin must fail; (4) relFold skips the fingerprint check — the near-miss refusal must fail; (5) relUnfold splices without removing the ref — an equivalence test must fail. Independent hunt: fold/unfold under open-pattern hosts; refs inside comprehension bodies and insertion patterns (patterns are self-contained namespaces — do refs resolve at APPLICATION time? verify the rule resolves against ctx at replay, and a stored pattern containing a ref round-trips); canonicalizeFreePorts skips refs; deiteration of ref-containing copies. Plan-doc sync + verdict.

- [ ] APPROVED verdict recorded; plan-doc sync. Commit.

---

**Deferred (recorded):** open-pattern relation definitions; placing refs from the UI (relation-naming feature); restating bundled theorems with folded guards (Plan 11 final, next).
