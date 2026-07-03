# Plan 16: Diagonal comprehension occurrences — repeated arguments in abstraction and instantiation

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Comprehension abstraction and instantiation accept DIAGONAL occurrences — the same host wire serving multiple argument positions (abstracting φ(x,x) as R(x,x) under ∃R with G(a,b) := φ(a,b); instantiating a bubble at G with repeated attachment wires). The graph representation already supports the result (one wire may carry several arg ports of one atom — port partition permits it); only the rules refuse. The current gates: `applyComprehensionAbstract` throws `argument wires are not distinct`, and a diagonal occurrence's attachment count is below the comprehension's arity, tripping the count gate.

**The soundness core (the only part that matters):** rule 8's consistency check is what keeps second-order abstraction honest — each occurrence must BE the comprehension body on its argument wires, verified by boundary-pinned canonical form. For a diagonal occurrence the correct standard is the DIAGONALIZED comprehension: where argument positions i and j ride the same occurrence wire, the comp's boundary wires b_i and b_j are MERGED (endpoint sets unioned into one wire, scope unchanged — both are root-scoped boundary stubs), and the occurrence's extracted pattern (pinned by its distinct attachments in order of first appearance in `args`) must equal the diagonalized comp (pinned by the merged boundary in the same collapsed order). Witnessing is unchanged: R := G makes R(x,x) ⟺ G(x,x) — exactly the occurrence — so the equivalence argument of the non-diagonal case carries over verbatim. The diagonalization is computed on a COPY of the comp per distinct aliasing pattern; the stored comprehension is never mutated.

**Scope:** `applyComprehensionAbstract` + `applyComprehensionInstantiate` (the inverse direction must accept the same aliasing — splicing the comp body with repeated attachment wires merges the corresponding boundary stubs onto one host wire). Theorem-citation aliasing (`Plus(a,a,o)` style, currently refused by the matcher's used-images rule) is EXPLICITLY OUT — noted as the follow-up it unlocks, to be designed with the citation/splice semantics together.

### Task 1: Diagonalization + abstraction

**Files:** `src/kernel/rules/comprehension.ts` — a `diagonalize(comp, args-aliasing-pattern)` helper (pure; merges boundary wires per the pattern; returns the collapsed boundary order); `applyComprehensionAbstract` gates reworked: repeated `occ.args` allowed, count gate becomes `occ.args.length === comp.boundary.length` (arity, not attachment count) with every attachment used at least once; the consistency check compares against the diagonalized comp. Non-diagonal behavior byte-identical (diagonalize with no aliasing is the identity — pin it).
**Test:** `tests/kernel/rules/comprehension-diagonal.test.ts` — abstract φ(x,x) with a binary comp: the produced atom has both arg ports on one wire; a NEAR-diagonal (occurrence differs from the diagonalized comp by one node) refuses; aliasing patterns beyond pairs (triple x,x,x; mixed x,x,y); the identity pin (no-aliasing diagonalize = same form); polarity gate unchanged; every existing comprehension test green untouched.

- [ ] Abstraction + tests green; suite + tsc green. Commit.

### Task 2: Instantiation + replay road

**Files:** `applyComprehensionInstantiate` accepts repeated attachments (splice merges the aliased boundary stubs onto the shared host wire — verify spliceSubgraph's behavior and gate loudly if it needs work); proof-step JSON unchanged in shape (args already carry the wire list; repeats now legal).
**Test:** instantiate-then-abstract round-trip on a diagonal case (the inverse pair is the correctness statement); JSON round-trip of a derivation containing a diagonal step through theoryToJson → loadTheory; the existing polarity/arity refusals still fire.

- [ ] Instantiation + round-trip green; suite + tsc + e2e green. Commit.

### Task 3: Review + close

- [ ] Independent adversarial review (kernel soundness surface): near-miss diagonal folds/abstractions must refuse (the diagonalized-form check is the linchpin — attack it: an occurrence matching the UNdiagonalized comp must not pass a diagonal-args call and vice versa; aliasing-pattern confusion between (0,1)-merge and (1,2)-merge on ternary comps); mutation probes on each reworked gate; replay sentinel (both theories).
- [ ] Plan-doc + memory sync; close. Note the unlocked follow-up: theorem-citation aliasing.
