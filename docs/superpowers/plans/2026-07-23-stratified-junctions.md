# Stratified Junctions — Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development task-by-task. Steps use checkbox (`- [ ]`) syntax.

**Goal:** Replace the junction subsystem with the accepted stratified-space model: wire state = (T, b, τ) on X, crossings via canonical φ under the ordinary gate, zero auxiliary mechanisms.

**Contracts:** `docs/superpowers/specs/2026-07-23-junction-problem-statement.md` (§1.5 formal statement, §6 acceptance, §7 boundary) and `2026-07-23-phi-construction.md` (canonical φ, corridor Lemma 1′, step-on-X pseudocode, §6 inventory). Physics corpus binds throughout; paradigm frozen.

**Architecture:** State refactor first (topology as stored coordinate), then the sweep extension (ℓ_e ≥ 0 boundary + φ crossing), then deletions, then the re-derived tests, then the two front-loaded empirical verifications (crossing timescale; mid-transition looks → user).

## Global Constraints

- Strict descent untouched in meaning: every accepted move strictly lowers total E; no triggers/throttles/repair moves/carry policies — mechanism-count zero, audited at review.
- The elastica leg solver, its caches, barrier/clearance energies, and all law tests are load-bearing: keep verbatim/green.
- Explicit-path staging; full `npm run test:all` + tsc 0 at each task boundary (physics suite included from Task 3 on; Tasks 1–2 file-local + owned-set, `tsc-errors: N` recorded).
- No commits to `examples/*.json`; the untracked gallery script stays untracked.

---

### Task 1: Wire junction state = (T, b, τ)

**Files:** `src/view/engine.ts` (wire structure: explicit topology T — adjacency as stored data; branch positions; per-half-edge tangent angles; `mkEngine` seeds via soaptree, birth-only), `src/view/wires.ts`, carryOver (`engine.ts:456-473` era): carry T explicitly for surviving wires (keyed on wire identity, not branch count — kills diagnosed cause (a) structurally). Tests: engine/wires suites adapt; a new carry test: rebuild after a rewrite preserves T (the revised repro (a) from `junction-app-path.test.ts` goes green here or in Task 4).
- [ ] TDD per house rules; file-local green; commit `feat: junction state as (T,b,tau)`.

### Task 2 (REVISED after preservation-bias correction): spec-literal state-model replacement

**The cut:** `Wire` state becomes exactly (T, b, τ) per the formal spec §1.5.
DELETED AS CONCEPTS (not renamed, not wrapped): the `'junction'` BodyKind and
all hub entities (engine.ts:323 era, hub kinds, tip/slot junction structures
EXCEPT ∃-tip bodies which are corpus law); `branches` as a model object;
`tryTopologyMove`/`checkedSet`/edge-trigger/deferral (relax.ts:1233-1586 era);
any crossing-as-event, detection radius, or per-sweep cap. Junction geometry
(where legs meet) is computed at render/solve time from (T, b, τ), stateless,
downstream. KEPT because law mandates them: leg solver + caches (curve law),
barrier/clearance energies (plan-22 measurements), ∃-tip bodies (dangling-end
law), term/atom/anchor bodies. Proposals that drive an internal edge through
ℓ_e = 0 map through canonical φ as ORDINARY coordinate moves under the
ordinary gate — nothing detects, nothing fires. Task 1's carryOver carries
(T, b, τ) unchanged in spirit; its "junction state" vocabulary is renamed.
The untracked `tests/physics/junction-crossing.test.ts` (salvage from the
reverted attempt) is evaluated: adopt, adapt, or delete with reasons.

- [ ] TDD; physics suite green via FOREGROUND per-file runs; tsc 0; commit(s)
  with honest headlines. CONTROLLER VERIFIES THE TREE DIFF PERSONALLY before
  any deletion claim is relayed; the reviewer independently confirms the
  deletion list against the tree.

### Task 3 (REVISED): face-reachability re-measurement on the clean model

The reverted attempt reported crossings unreachable (ℓ_e floors ~0.15 wu;
elastica prefers separated Y-Y). That measurement is SUSPECT: it was taken on
the grafted substrate where junction BODIES carried their own physics
(barriers/clearance) that may have been exactly what floored the gap. Re-run
the reachability probes on the clean model: does ℓ_e reach 0 under drags/
squeezes now? Report distributions. If reachable: the corridor design works
as specced — proceed. If still floored: STOP; present the three user options
(visibility-scale ε with derived constant / sticky-topology-as-correct /
energy-balance question) with the clean numbers — the user rules.

### Task 4: acceptance tests per problem-statement §6 (unchanged content)

Trajectory continuity; interactive crossing-through-zero (contingent on Task
3's verdict); carry; within-basin bar-tangent freedom; law suite green.

### Task 5: front-loaded empirical verification for the user (unchanged)

Timescale numbers + mid-transition drag renders delivered to the USER; STOP
for the visual ruling. Whole-branch SDD review with mechanism-count audit
(zero auxiliary) and an independent tree-verified deletion audit.

## Verification

Full suites + tsc 0; §6 acceptance; mechanism count zero; deletion list
verified against the tree by controller AND reviewer independently; the
user's visual ruling is the final gate.
