# Signature-Indexed Wires — TS Sweep Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Replace SO quantifier bubbles with signature-indexed wires across the entire TypeScript package — kernel types, canonical form, subgraph algebra, rules, app, and view — leaving every test green.

**Architecture:** One wire concept `{scope, sig, endpoints}` with `Sig ::= term | rel(Sig…)`. Atoms designate their relation via a head port on a relational wire. Comprehension bodies are node payloads mirroring λ-term nodes. Five primitive rules (vacuous, body attach/detach, fold/unfold, join, structural) replace the monolithic comprehension rules, which survive only as app-level macros. Bubbles, binder fields, binder spines, and open-binder matching are deleted.

**Tech Stack:** TypeScript 5.5, Vitest 2.

**Spec:** `docs/superpowers/specs/2026-07-22-signature-indexed-wires-design.md`

**Execution context:** run in a fresh worktree created from `main` via the `superpowers:using-git-worktrees` skill (branch `feature/signature-indexed-wires`). Plan 2 (Lean rearchitecture) follows on the same branch.

## Global Constraints

- Terminology: atoms are "atoms", never "application nodes"; the occurrence rule is "fold/unfold", never "β" (β/η are term-language only). This binds identifiers, comments, and commit messages.
- After the final task, `grep -rn "bubble\|binder" src/` returns no hits (docs/ excluded); no compatibility shims, re-exports, or legacy paths anywhere.
- The λ-term language (`src/kernel/term/`) is untouched by every task.
- Signature equality is structural and exact; no subtyping, no coercions.
- Each task ends with the full suite green: `npx vitest run`.
- Old comprehension-rule test scenarios are preserved by porting them to macro composites (Task 11), never deleted without replacement.

---

### Task 1: Sig module

**Files:**
- Create: `src/kernel/diagram/sig.ts`
- Test: `tests/kernel/diagram/sig.test.ts`

**Interfaces:**
- Produces:
  - `type Sig = { readonly kind: 'term' } | { readonly kind: 'rel'; readonly args: readonly Sig[] }`
  - `type RelSig = Extract<Sig, { kind: 'rel' }>`
  - `const TERM: Sig` (the shared `{kind:'term'}` value)
  - `relSig(args: readonly Sig[]): RelSig`
  - `sigEquals(a: Sig, b: Sig): boolean` (structural)
  - `sigKey(s: Sig): string` — canonical injective string: `'t'` for term, `'(' + args.map(sigKey).join(',') + ')'` for rel
  - `sigOrder(s: Sig): number` — 0 for term, `1 + max(0, ...args.map(sigOrder))` for rel
  - `assertWellFormedSig(s: unknown): asserts s is Sig` — loud rejection of malformed values (non-array args, missing kind)

- [ ] **Step 1: Write failing tests** — `sigEquals` structural on nested sigs; `sigKey` injective across `rel()`, `rel(term)`, `rel(rel(term), term)` (the `Arrow` sort `((ι),(ι),ι)` spelled `relSig([relSig([TERM]), relSig([TERM]), TERM])`); `sigOrder` = 0 / 1 / 2 on those; `assertWellFormedSig` throws on `{kind:'rel', args: 'x'}`.
- [ ] **Step 2: Run, verify FAIL** — `npx vitest run tests/kernel/diagram/sig.test.ts` (module not found).
- [ ] **Step 3: Implement** the module exactly per the interface block.
- [ ] **Step 4: Run, verify PASS.**
- [ ] **Step 5: Commit** — `feat: add signature grammar for wires`

### Task 2: Core diagram types

**Files:**
- Modify: `src/kernel/diagram/diagram.ts`
- Test: `tests/kernel/diagram/diagram.test.ts` (rewrite bubble/binder cases)

**Interfaces:**
- Produces (consumed by every later task):
  - `Region = {kind:'sheet'} | {kind:'cut'; parent}` — bubble kind deleted.
  - `Port = {kind:'output'} | {kind:'freeVar'; name} | {kind:'arg'; index} | {kind:'head'}`; `portKey` gains `case 'head': return 'hd'`.
  - `Wire = { readonly scope: RegionId; readonly sig: Sig; readonly endpoints: readonly Endpoint[] }`
  - Atom: `{ kind:'atom'; region: RegionId; sig: RelSig }` (binder deleted; sig inline so `requiredPorts` stays context-free).
  - Ref: `{ kind:'ref'; region: RegionId; defId: string; sig: RelSig }` (arity replaced; named defs may now have higher sorts).
  - Body node: `{ kind:'body'; region: RegionId; sig: RelSig; content: DiagramWithBoundary }` — mirrors `TermDiagramNode`: payload fingerprinted, not inlined. `content.boundary[0..sig.args.length)` are the argument stubs; remaining boundary wires are parameters exposed as freeVar ports `p0, p1, …` in order.
  - `requiredPorts`: term unchanged; atom → `[{kind:'head'}, arg 0..sig.args.length)`; ref → arg ports per `sig.args.length`; body → `[{kind:'output'}, freeVar p0..pk)`.
  - `portSig(node, port): Sig` — the sort a port accepts: term-node ports all `TERM`; atom head = `node.sig`, atom arg i = `node.sig.args[i]`; ref arg i = `node.sig.args[i]`; body output = `node.sig`, body freeVar pj = sig of `content.boundary[argCount + j]`.

- [ ] **Step 1: Write failing tests** — atom requires head+arg ports from inline sig; `mkDiagram` rejects: wire whose sig ≠ `portSig` at any endpoint (`wire 'w' sig mismatch at port 'hd' of node 'a'`), body node whose boundary is shorter than `sig.args.length`, second sheet still rejected; accepts a depth-2 atom (`Arrow` sort head wire + two order-1 arg wires + one term arg wire). Every port sort must be checked — a term wire into an order-1 arg port fails loudly.
- [ ] **Step 2: Run, verify FAIL.**
- [ ] **Step 3: Implement** — delete bubble from `Region` and its arity validation; delete atom binder validation (`diagram.ts:264-269`); add `portSig` and the per-endpoint sig-equality check in the wires loop (alongside the existing scope-enclosure check at `diagram.ts:324-326`); validate body content recursively via `mkDiagramWithBoundary` invariants; keep `canonicalizeFreePorts` untouched (body freeVar ports are already canonical `p0…` by construction — validate, don't rename).
- [ ] **Step 4: Compile the package** — `npx tsc --noEmit` will fail across dependents; that is expected and drives Tasks 3–10. Run only this test file: PASS.
- [ ] **Step 5: Commit** — `feat: signature-indexed wires in core diagram types` (commit even with downstream compile errors; the branch is the atomic unit, and each subsequent task shrinks the error set — full-suite green is the Task 10 exit gate, applied to every task only from Task 10 on).

Amendment to Global Constraints: Tasks 2–9 gate on their own test files passing plus a shrinking `npx tsc --noEmit` error inventory (record the count in each commit message); Tasks 10–12 gate on the full suite.

### Task 3: Regions, boundary, builder, spawn

**Files:**
- Modify: `src/kernel/diagram/regions.ts` (delete bubble branches; polarity logic already cut-only), `src/kernel/diagram/boundary.ts` (boundary wires of any sig; root-scoped law unchanged), `src/kernel/diagram/builder.ts` (`atom(region, sig)` replaces `atom(region, binder)`; delete bubble constructor; add `relWire(scope, sig)`), `src/kernel/diagram/spawn.ts` (`spawnBoundRelationNode` attaches a fresh atom's head port to a designated relational wire)
- Test: corresponding test files, same rewrite.

- [ ] Steps: failing tests for builder atom+relWire round-trip through `mkDiagram`; implement; run file-local tests PASS; commit `feat: sig-aware builders and boundaries`.

### Task 4: Canonical form

**Files:**
- Modify: `src/kernel/diagram/canonical/explore.ts`
- Test: `tests/kernel/diagram/canonical/*.test.ts`

- [ ] **Step 1: Failing tests** — (a) two diagrams that differ only by old-world quantifier nesting order (now: two relational wires at the same scope, constructed in either insertion order) yield identical `exploreForm`; (b) wires of different sig at the same scope yield different forms (`sigKey` enters the wire color); (c) body nodes with canonically-equal content fingerprint equal, different content different.
- [ ] **Step 2–4:** Delete `regionKindKey` bubble branch (`explore.ts:160`) and the atom `b:` binder signature (`explore.ts:191,295`); wire color becomes `scopeColor + '|' + sigKey(sig)`; atom node color = `'atom|' + sigKey(sig)`; body node color = `'body|' + sigKey(sig) + '|' + boundaryForm(content)` (the same payload-fingerprint pattern term nodes use via shape keys). Head-port incidences flow through the existing wire-endpoint refinement with `portKey 'hd'`. File tests PASS.
- [ ] **Step 5: Commit** — `feat: canonical form over signature-indexed wires`

### Task 5: Subgraph algebra

**Files:**
- Modify: `src/kernel/diagram/subgraph/match.ts`, `extract.ts`, `splice.ts`, `occurrence-certificate.ts`, `selection.ts`
- Test: corresponding suites.

**Interfaces:**
- Produces: `extractSubgraph` return type loses `binderStubs` entirely — an atom whose head wire lies outside the selection contributes that wire as an ordinary attachment (boundary) wire, uniformly with arg wires. `spliceSubgraphMapped` loses the `binderMap` option. Matching requires `sigEquals` on corresponded wires; binder-identity checks (`match.ts:302-315`), open-binder pure-chain logic (`match.ts:200-226`), and stub-bubble chain reconstruction (`extract.ts:50-81`) are deleted.

- [ ] **Step 1: Failing tests** — extraction of a lone atom bound outside the selection yields a pattern whose boundary includes a relational stub of the atom's sig (this exact scenario is today's `binderStubs` error path — the new test asserts success and the stub's sig); match refuses to correspond wires of unequal sig; splice lands a relational boundary stub onto a host relational wire of equal sig and refuses unequal.
- [ ] **Step 2–4:** Implement by deletion + the sig-equality gate; boundary wires already carry sig from Task 2. File tests PASS.
- [ ] **Step 5: Commit** — `feat: sig-uniform subgraph algebra; delete open-binder machinery`

### Task 6: Primitive rules — vacuous and join

**Files:**
- Modify: `src/kernel/rules/vacuous.ts` — bubble intro/elim becomes endpoint-free-wire intro/elim: `applyVacuousIntro(d, scope, sig, reservation?)` adds `{scope, sig, endpoints: []}` at any polarity; `applyVacuousElim(d, wireId)` requires `endpoints.length === 0` (loud refusal otherwise). Sound both polarities per spec (nonempty domains).
- Modify: the wire-join rule site (locate via `joinWires` / congruence-join usages in `src/kernel/rules/`; `src/kernel/diagram/edit.ts:107-111` computes merged scope) — add the `sigEquals` gate with message `cannot join wires of different signatures`.
- Test: `tests/kernel/rules/vacuous.test.ts` + join suite.

- [ ] Steps: failing tests (vacuous intro at positive AND negative scopes both succeed for `TERM` and `relSig([TERM])`; elim refuses a wired endpoint; join refuses `TERM` vs `relSig([TERM])`), implement, file tests PASS, commit `feat: vacuous wire intro/elim and sig-gated join`.

### Task 7: Primitive rules — body attach/detach

**Files:**
- Create: `src/kernel/rules/body.ts`
- Test: `tests/kernel/rules/body.test.ts`

**Interfaces:**
- Produces:
  - `applyBodyAttach(d, wireId, content: DiagramWithBoundary, params: readonly WireId[], orientation: 'forward'|'backward' = 'forward', reservation?): Diagram` — inserts a body node at the wire's scope region, output port onto `wireId`, freeVar ports onto `params`. Gates: `d.wires[wireId].sig` is `rel` with `content.boundary.length === sig.args.length + params.length`; each `params[j]` wire's scope is at-or-outside the target wire's scope (the spec's comprehension gate — note *at-or-outside*, deliberately admitting same-region parameters, unlike the old strictly-outside gate) and `sigEquals(params[j].sig, portSig(bodyNode, freeVar pj))`; polarity gate mirrors `applyComprehensionInstantiate` (`comprehension.ts:156-159`): forward requires the wire's scope polarity `negative`, backward `positive` — one boolean flip, shared code path.
  - `applyBodyDetach(d, bodyNodeId, orientation = 'forward')` — removes the body node (inverse gate), leaving the wire and params untouched.
- One wire may carry at most one body node: attach refuses if any body node's output endpoint already lies on `wireId` (`wire 'w' already carries a body`).

- [ ] Steps: failing tests for the gate matrix (arity mismatch, param sig mismatch, param scope inside target scope refused, same-region param accepted, polarity refusals both orientations, double-attach refusal), implement, file tests PASS, commit `feat: body attach/detach primitive`.

### Task 8: Primitive rules — fold/unfold

**Files:**
- Create: `src/kernel/rules/fold.ts` (absorbing the named-relation unfold from its current site — locate via `defId` usage in `src/kernel/rules/`; one implementation, two body sources)
- Test: `tests/kernel/rules/fold.test.ts`

**Interfaces:**
- Produces:
  - `applyUnfold(d, atomId, resolve: (defId: string) => DiagramWithBoundary | undefined, reservation?): Diagram` — for an atom whose head wire carries a body node, or a ref with a resolvable `defId`: splice a copy of the body content at the atom's region (arg-stub i onto the atom's arg-i wire, param stubs onto the body node's own param wires), then drop the atom (`dropNode` pattern, `comprehension.ts:113-123`). Polarity-free (definitional rewriting). Refuses an atom whose head wire has no body (`atom 'a' head wire carries no body to unfold`).
  - `applyFold(d, occurrence: SubgraphSelection, args: readonly WireId[], target: {wireId} | {defId}, reservation?)` — inverse: verify the occurrence's boundary-pinned fingerprint equals the body content's (the `exploreForm` comparison pattern at `comprehension.ts:363-366`, including diagonal aliasing via shared arg wires), delete the occurrence, insert an atom on the target wire/ref.
- Diagonalization is *not* a rule: repeated `args` entries simply plug one wire into several arg ports; the old `diagonalize` helper survives only as a pure boundary-aliasing utility inside fold's fingerprint comparison.

- [ ] Steps: failing tests — unfold a bodied atom at positive AND negative polarity (both succeed); unfold splices params correctly; fold round-trips unfold on the same diagram (canonical forms equal); diagonal case `R(x,x)` unfolds with both stubs on one wire; ref unfold behavior matches the old named-relation tests (port those cases here). Implement, file tests PASS, commit `feat: fold/unfold over bodied wires and named refs`.

### Task 9: Kernel serialization and proof steps

**Files:**
- Modify: `src/kernel/diagram/json.ts` (drop bubble region + binder atom codecs `json.ts:83-85,109-111`; add sig codec via `assertWellFormedSig`, wire sig field, body node codec with recursive content), `src/kernel/proof/json.ts` (replace `comprehensionInstantiate`/`comprehensionAbstract` step payloads `proof/json.ts:264-266,313,354-356,438-455` with the five primitive step kinds: `vacuousIntro`, `vacuousElim`, `bodyAttach`, `bodyDetach`, `unfold`, `fold`, and the sig-gated join payload), delete `src/kernel/rules/comprehension.ts` and its test file (scenarios move to Task 11).
- Test: round-trip suites for both codecs.

- [ ] Steps: failing round-trip tests (diagram with depth-2 atom + body node survives encode/decode identically; decoding a payload containing `"bubble"` or `"binder"` fails loudly as unknown), implement, file tests PASS, commit `feat: serialize sigs, bodies, and primitive steps; delete monolithic comprehension rules`.

### Task 10: App adaptation

**Files:**
- Delete: `src/interaction/comprehension-dependencies.ts`, `tests/interaction/comprehension-dependencies.test.ts` (the proxy/host spine model has no counterpart).
- Modify: `src/interaction/named-relation.ts` (gate on wire sig instead of `target.kind==='bubble'`), `src/theories/macros.ts` (`spawnBoundRelation` targets a relational wire), `src/app/edit.ts` (`addBubble` → `addRelationWire(scope, sig)`; bubble dissolution branch in `deleteSelection` deleted — deleting a relational wire's last atom leaves an endpoint-free wire, deletable by vacuous elim), `src/app/actions.ts` (`vacuousElim` targets wires), `src/app/proof-front.ts` (`bubbleHues` → order-ladder color lookup; `openComprehension` flows target wires), `src/app/interact/moves.ts`, `src/app/interact/spawn.ts`, `src/app/interact/proof-spawn.ts` (binder enumeration/colors → relational-wire enumeration; hover targets wires), `src/app/relation-workspace.ts`, `relation-workspace-draft.ts`, `relation-transactions.ts` (the workspace authors `DiagramWithBoundary` bodies; host-binder import becomes param-wire designation).
- Test: `tests/app/*` rewrites in kind.

- [ ] Steps: rewrite failing app tests to the wire model scenario-by-scenario (each old bubble scenario has a wire counterpart; none dropped), implement, **full suite + `npx tsc --noEmit` green from here on**, commit `feat: app layer over signature-indexed wires`.

### Task 11: Macro layer and conservativity replay

**Files:**
- Create: `src/app/interact/comprehension-macros.ts`
- Test: `tests/app/comprehension-macros.test.ts`

**Interfaces:**
- Produces: `macroComprehensionInstantiate(d, wireId, comp, params, orientation, reservation)` = `applyBodyAttach` → `applyUnfold` per atom on the wire → `applyVacuousElim`; `macroComprehensionAbstract` = the inverse composite (vacuous intro → folds → detach-free, since abstraction introduces no body — fold against an explicit `comp` fingerprint).

- [ ] **Step 1:** Port every scenario from the deleted `tests/kernel/rules/comprehension.test.ts` (Task 9) to the macro API, asserting the same resulting canonical forms as the old expectations. These are the conservativity witnesses; failing first because the module doesn't exist.
- [ ] **Step 2–4:** Implement the composites; suite PASS. Also add the new-power test: instantiate with one occurrence left folded (wire persists with body; canonical form differs from full expansion; a later `applyUnfold` completes it).
- [ ] **Step 5: Commit** — `feat: comprehension macros; replay old rule scenarios as composites`

### Task 12: View adaptation

**Files:**
- Modify: `src/view/paint.ts` (delete bubble ring painting `paint.ts:203-207` and `bubbleHues`; wire stroke color = order ladder `sigOrder(sig)` → palette index, term wires keeping today's wire color as rung 0; atom body stroke = its head wire's rung; `highlightGroup` keys on shared head wire instead of `binder===`), `src/view/engine.ts` (atom geometry arity from `node.sig.args.length`, not `d.regions[n.binder]`), `src/view/bend.ts` (`atomGeometry` gains the head-port anchor), `src/view/constraints.ts` / `src/view/relax.ts` (bubble region circles no longer exist; relational wires enter the existing wire-physics as additional wire species; body nodes are ordinary sealed node bodies).
- Test: view suites in kind.

- [ ] Steps: failing tests for the paint mapping (order-0/1/2 wires get three distinct ladder entries; no code path consults regions for atom geometry), implement, **full suite green**, run the app via the `run` skill and visually confirm a depth-2 diagram renders (atoms, ladder colors, a sealed body node), commit `feat: render signature-indexed wires with order-ladder colors`.

---

## Self-review notes

- Spec coverage: representation (T1–T3), canonical/matching (T4–T5), five primitives (T6–T8; structural rules untouched by design), serialization/migration (T9), app (T10), conservativity + gained flexibility (T11), rendering (T12). Lean sections deferred to Plan 2 by design.
- The Task 2 green-gate amendment is deliberate: a root-type swing cannot keep the whole package compiling task-by-task; the tracked-error-count discipline replaces it until Task 10.
- `portSig` is defined once (Task 2) and consumed by Tasks 5–8; `sigEquals`/`sigKey`/`sigOrder` defined once (Task 1).
