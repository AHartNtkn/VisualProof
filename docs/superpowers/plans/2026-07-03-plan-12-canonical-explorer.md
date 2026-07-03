# Plan 12: The canonical explorer — labeling, isomorphism, and matching as one engine

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Replace the exhaustive-backtracking occurrence matcher (`subgraph/match.ts` — factorial on interchangeable items, wiring checked only post-hoc, bare boundary wires refused) and the separate fingerprint machinery with ONE canonical-exploration engine. USER DESIGN (2026-07-03, their framing): our diagrams are port-hypergraphs — nodes carry ORDERED ports, so exploration from a given anchor is deterministic, and canonical labeling / isomorphism / subgraph matching are all polynomial. General-graph NP-hardness does not apply: it comes from unordered neighborhoods, which our nodes do not have.

**The algorithm (user's sketch, mapped to our model):**
- Explore (BFS/DFS) from the anchor: for an OPEN diagram the boundary order is given — start at the boundary wires; for a CLOSED one, canonically chosen starts per component (connected: linear; disconnected: quadratic).
- Reaching a node orders its remaining incident wires (positional port keys) — they enter the queue in canonical order. Relabel everything in encounter order: the labeling is a COMPLETE INVARIANT.
- The equality nodes — our WIRES — cannot order their endpoints: crossing a multi-endpoint wire enqueues the continuation as a SET. Defer sets while any determined exploration is pending (it usually reaches and labels set members from elsewhere, breaking the symmetry). When a set must be explored: one layer at a time, nauty-style partition refinement, maintaining indistinguishability sets. Only when a layer maps a set into itself (genuine automorphism) is a choice made: lexicographically least labeling. Rare in practice.
- REGIONS are the second unordered-set source: sibling cuts/bubbles enter as sets under the same machinery (a region connects unordered to its children and members). Twin empty cuts are the canonical lex-least case.

**USER RULING — βη is optional, never in the invariant:** isomorphism is NOT up to βη ("that complicates things and can also make intuition for matching harder"). Canonical labeling and isomorphism use EXACT term comparison: structural de Bruijn equality (α-equivalence is literal identity), free ports by name-blind positional role ([[port-names-are-not-semantic]]). The labeling is therefore total, deterministic, fuel-free. MATCHING takes a mode parameter: `exact` (same comparison; the user converts first if they want looseness — that is what the conversion rule is for) or `betaEta` (node-compatibility relaxed modulo βη with the existing fuel + `undecided` reporting contract, preserved verbatim). Existing rules keep their current semantics (βη where they have it today) so every recorded derivation replays unchanged; migrating rules toward exact-mode is downstream design space this parameterization deliberately keeps open.

**Modes:**
1. **Canonical labeling** — the invariant. Replaces `canonical/fingerprint.ts`'s role (relFold's boundary-pinned occurrence check, dedup) after Task 3 proves agreement.
2. **Isomorphism** — labeling comparison.
3. **Occurrence matching** — run the pattern's canonical exploration AGAINST the host: each determined pattern step dictates the unique host continuation via the same port keys. Citation-supplied argument wires seed the boundary anchors directly; a BARE boundary wire is an anchor with no forced endpoints (the succShiftS-era wart dies by construction). Unseeded uses enumerate host anchor candidates for the first boundary edge — polynomially many starts, each ~linear. Pattern-side automorphisms surface as the same set machinery; occurrences dedup by footprint as today.

**Contracts preserved:** `Occurrence`/`MatchResult` shapes; completeness modulo `undecided` (betaEta mode only — exact mode has no undecided); open-binder semantics; footprint dedup. NO DUAL SYSTEMS: `subgraph/match.ts`'s backtracking search and the superseded fingerprint path are DELETED at the end, all consumers moved.

### Implementation findings (worker)

- **Labeling = the existing individualization-refinement, reframed.** The user's anchored exploration and `canonical.ts`'s refinement are the SAME computation on the labeling: ordered ports enter refinement as port-keyed neighborhood signatures; unordered wire-endpoint / sibling-region sets are exactly the tied colour classes that refinement resolves without a choice; a genuine automorphism is a class refinement cannot split, resolved by individualization + lex-least. Because any two complete invariants induce the same iso-partition, the Task 3 corpus agreement is *guaranteed* to hold iff the new labeling is a correct complete invariant — the agreement test is the completeness oracle, not a coincidence. The new engine therefore preserves the proven refinement backbone (soundness-critical for relFold) rather than risking a fresh, unproven canonicalizer; the exploration framing is realised as pin-seeded initial colours + refinement.
- **The genuine, benchmarked win is the matcher.** `subgraph/match.ts`'s factorial cost comes from enumerating interior bijections of interchangeable items and checking wiring post-hoc. The exploration matcher drives the pattern's canonical order against the host so determined steps never branch, and automorphic pattern classes collapse to one footprint instead of N! enumerations.

### Task 1: The engine

**Files:** `src/kernel/diagram/canonical/explore.ts` (the exploration core: queue with determined entries + deferred sets, layer refinement, indistinguishability partitions, lex-least tiebreak; term-label function parameterized `exact | betaEta`), labeling + isomorphism modes on top.
**Test:** `tests/kernel/canonical/explore.test.ts` — invariance (relabeled/reordered isomorphic diagrams get identical labelings; non-isomorphic differ — property test vs brute-force reference written independently in the test), boundary-order sensitivity for open diagrams, wire-set deferral observed (a symmetric wire broken by a pending determined path takes no lex-least choice), twin-empty-cut lex-least determinism, exact-mode term comparison is name-blind but NOT βη (`λx.x` applied vs its redex differ).

- [x] Engine + labeling + isomorphism green; full suite + tsc green. Commit. — `canonical/explore.ts` (`exploreLabeling`/`exploreForm`/`exploreIso`); `tests/kernel/diagram/explore.test.ts` (8 tests: brute-force property oracle over ~1830 random pairs + 80 relabelings, boundary-order sensitivity, wire-set deferral, twin-empty-cut lex-least, exact-not-βη). tsc clean, 770/770.

### Task 2: Matching mode + consumer migration

**Files:** occurrence matching over the engine; `findOccurrences` keeps its signature plus the attachment seed and the mode parameter; every consumer (iteration/deiteration justification, theorem citation, comprehension, relFold occurrence check) migrated with their CURRENT comparison semantics (βη where today's behavior is βη — recorded derivations must replay byte-identical); bare-boundary support live (the artificial-consumer workarounds in theory derivations may now be simplified ONLY if statements stay identical — otherwise leave and note).
**Test:** the ENTIRE existing matcher battery green unchanged (it is the semantic contract); new: bare-boundary citation case; seeded-vs-unseeded agreement; benchmark test with a visited-state counter — N identical sibling nodes and an N-endpoint equality wire, asserting linear-ish growth where the old matcher is factorial (pin the counts).

- [ ] Matching green, all consumers migrated, old backtracking matcher DELETED, suite + tsc + e2e green. Commit.

### Task 3: Fingerprint unification + review

- [ ] Spike-prove labeling agreement with `diagramFingerprint`/`boundaryFingerprint` across the full bundled corpus (every theorem side, every relation body, every replay step of both theories) BEFORE deletion; then relFold + dedup move to the labeling and the old fingerprint path is deleted. (relFold's gate is soundness-critical: agreement is proven, not assumed.)
- [ ] Independent adversarial review (reviewer wrote none of it): soundness probes on relFold's new gate (a near-miss occurrence must still refuse); mutation probes (skip set-deferral → symmetric case mislabels; break lex-least determinism → invariance test fails; drop a port key → collision test fails); benchmark honesty (counter can't be gamed); JSON-road replay of both theories.
- [ ] Plan-doc + memory sync; close.
