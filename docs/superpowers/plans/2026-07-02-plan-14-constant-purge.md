# Plan 14: The Constant Purge — named definitions are nodes, never term syntax

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Enforce the USER LAW (memory: `named-defs-never-inside-terms`, 2026-07-02): *"Relations are ALWAYS AND ONLY EVER THEIR OWN NODES … THERE ARE NO NODES ASSOCIATED WITH LAMBDA EXPRESSIONS … The definition of named relations can expand to diagrams that include lambda expressions, but THAT'S IT."* The violation that exposed the wrong model: dragging a λ-term body dragged its satellite constant discs with it — because the KERNEL term language contains constants inside terms.

**The target model:**
- λ-term nodes carry PURE λ-terms: `bvar | port | lam | app`. The `const` constructor is deleted from the term language.
- Every named definition is a RELATION: a ref node `{kind:'ref', defId, arity}` whose definition is a `DiagramWithBoundary`. Function constants become relations with an output place: `Zero/1`, `Succ/2`, `Plus/3`. The defining diagram wires a closed pure-λ program node to a use-site term node by a line of identity (e.g. Plus(a,b,c) := ∃p. p = ⟦λm n f x. m f (n f x)⟧ ∧ c = p a b).
- Connections between named nodes and λ-term nodes happen ONLY by shared wires (lines of identity). Definitional computation happens by `fusion` (the one-point rule, inlines a producer along its wire) + `conversion` (βη) + `fission` (extract), replacing the deleted term-level `unfold`/`fold`.
- The renderer's satellite mechanism (constant discs attached to term bodies) is deleted with the glyphs that fed it. Nothing is ever visually attached to a λ-term's anatomy.

**Ordering constraint:** the restated theories only use machinery that already exists (relUnfold/relFold, fusion/fission, conversion, closedTermIntro, comprehension, congruenceJoin, headStrip). So the theories are restated FIRST on the current kernel — the suite stays green at every commit — and the purge lands second, compiler-driven, once nothing references constants.

### Task 0: Spike — one relational derivation end to end

De-risk the machinery before committing to the restatement: in a scratch vitest, define `Zero/1` and `Plus/3` as relations (defining diagrams with internal program wires), state relational `plusLeftUnit` (lhs: Zero(z) ∧ Plus(z,a,o); rhs: the o and a boundary ports riding one wire), and derive it via relUnfold → fusion → conversion → wire joins. Record the exact step sequence and every gate hit (fusion's single-consumer requirement, scope gates, boundary handling).

- [x] Spike green in a scratch test; findings recorded in this doc (§ Spike findings). Scratch deleted.

### Task 1: Relational restatement of the theories (current kernel, no purge yet)

**Files:** `src/theories/frege.ts` (relations `zero/1`, `succ/2`, `plus/3`, `nat/1` restated pure — the nat body uses Zero/Succ REF nodes per the user's round-3 directive, no bare λ in the definition; theorems `plusAssoc`, `plusLeftUnit`, `plusRightUnit`, `succShiftS`, `plusComm` restated relationally with the same names and re-derived), `src/theories/lambda.ts` (same treatment for whatever it defines), `src/theories/macros.ts` as needed.
**Test:** `tests/theories/*` batteries updated to the relational statements; `checkTheorem` green for every theorem; the battery asserts the statements contain NO `const` term anywhere (guards the coming purge).

- [x] All five arithmetic theorems re-derived relationally, batteries green, suite + tsc green. Commit (5fc60bc).

**Task 1 findings.** All five re-derived const-free (relUnfold/relFold + fusion/fission + conversion; no unfold/fold, definitions `{}`). Step counts: plusLeftUnit 5, plusRightUnit 5, plusAssoc 11, succShiftS 77, plusComm 62. lambda's onePlusOne/fixedPoint restated as pure-λ conversion theorems.
- **FLAGGED statement correction (succShiftS):** the target in Task 1 above labels the guard `nat(n)` with `Succ(n,s) ∧ Plus(m,s,o)` — i.e. the nat is on the SECOND Plus addend. That is NOT provable: `m + (S n) ~ S(m + n)` is not βη and needs induction on the FIRST addend (Church PLUS recurses on arg 1); `(S m) + n ~ S(m + n)` is the pure one (verified directly). The shipped statement guards the first Plus argument: `nat(a) ∧ Succ(b,sb) ∧ Plus(a,sb,o) ⟹ nat(a) ∧ Plus(a,b,t) ∧ Succ(t,o)`, boundary [a,b,o], sb/t internal. plusComm cites it with a:=b (its ℕ(b) guard). Same math, corrected guard placement.
- plusComm cites the RELATIONAL succShiftS (not a pure helper) via fold-cite-unfold at the closure step: the manufactured `b + (Sy)` node is iterated (one copy kept for the Cl fact), the copy folded to Succ/Plus refs, succShiftS applied forward, the produced Plus∧Succ unfolded back to `S(b + y)`.
- Deleted: `fregeDefinitions`, `lambdaDefinitions`, `deriveConversion`/`ConversionRecipe` recipe machinery, and their index.ts re-exports (no external consumers). natRelation() kept exported.
- Battery gains a no-const guard walking every theorem lhs/rhs + relation body of both theories.

### Task 2: The purge (kernel + view + app)

**Files:** `src/kernel/term/term.ts` (`const` constructor deleted; `cnst` deleted), knock-ons compiler-surfaced in `parse.ts` (constNames parameter deleted — `parseTerm(s)`), `print.ts`, `serialize.ts`, `reduce.ts`, `hnf.ts`, `path.ts`, `matchkey.ts`, `shape.ts`; `src/kernel/rules/definitions.ts` DELETED (applyUnfold/applyFold, Definitions type); proof steps `unfold`/`fold` deleted from `step.ts` + `json.ts`; `ProofContext.definitions` deleted; `headstrip.ts` const-head refusal branch deleted (unreachable); `src/view/tromp.ts`/`bend.ts` glyph geometry deleted; `src/view/engine.ts` Satellite type + satellites deleted; `paint.ts`/`hittest.ts` satellite painting/hit targets deleted; `src/app/boot.ts`/`shell.ts`/`tactics.ts` constNames plumbing deleted; `store.ts`/`persist.ts` theory JSON format drops definitions (no legacy readers — the format changes, the emitters regenerate).
**Test:** law battery gains: mkEngine produces zero satellites for every bundled diagram (the concept is gone — the test asserts the display list contains labels ONLY at ref-node discs); serialization round-trips have no const case; full suite + tsc green with the deletions (no wrappers, no re-exports).

- [x] Purge complete, acceptance grep empty, suite + tsc + e2e green. Commit (a0a645a).

**Task 2 aftermath (post-purge hardening, commit 54f3fe4).** Long-horizon probes on the relational plusComm replay exposed layouts that passed the 2600-tick at-rest battery but resumed creeping later: empty leaf regions (double-cut steps) carried positional state but participated in NO forces — only projections could move them, nothing restored them, and a dangling empty cut inflated its parent circle into permanent violation (standing conveyor, nonzero net momentum). Fixed by UNIFICATION: every empty leaf region gets an invisible `anchor` body at mkEngine, making bodies the only positional state — the preserved-center branch, shiftSubtree center mutation, dual carrier bookkeeping, and drag emptyLeaves all deleted. Also: warm-started minimal-circle recomputes (an order of magnitude off the per-tick projection cost — a single-sweep-per-tick variant was tried and REJECTED: partial projection leaves standing violations the forces feed on), and the boundary-exit aim is the outward radial through the body (continuous, θ-independent). Net momentum at rest is exactly (0,0); positions frozen over thousands of post-settle ticks; Playwright stress (190 replay steps, 2093 live frames) median draw 0ms max 6ms. A day-long red herring worth recording: the automation Chrome's hidden tabs wedge their renderer irrecoverably (survives navigation) — every apparent "app freeze" reproduced ONLY there; Playwright with live frames shows the app healthy.

### Task 3: Examples, e2e, review, sync

- [x] `scripts/emit-theories.ts` regenerates `examples/*.json` in the new format; e2e green; Playwright replay stress of relational plusComm through the live shell green.
- [x] Independent adversarial review: ISSUES-FIXED-APPROVED (commits 726b191, d993e43). All six mutation probes caught by existing tests. Findings fixed test-first: shell replay path (enterReplay/gotoReplayStep/carryOver) had zero automated coverage → new e2e spec; JSON round-trip per theorem of both theories added with a negative control (dropped step ⇒ loadTheory throws); anchor invisibility pinned (never painted/hit/drag-targeted); at-rest sample pinned to include an anchor-carrying step; fitCamera extracted with a positive-finite scale floor. 732/732, e2e 5/5.
- [x] Plan-doc sync; memory updated (`named-defs-never-inside-terms` integration state; `rendering-laws` interaction model). Work landed directly on main — no merge needed.

---

### Spike findings (Task 0)

Green first run (relational plusLeftUnit, 5 steps: relUnfold ×2, fusion ×2, conversion):
- A relation definition whose body wires a closed pure-λ program node to a use-site term node splices cleanly: `applyRelUnfold` merges the body's boundary stubs into the reference's arg wires, and the OUTER wire ids (the theorem's boundary) survive unfolding and fusion — `mkDiagramWithBoundary(cur, [wa, wo])` works on the final diagram with the original ids.
- `fusion`'s gates (exactly producer-output + one consumer-freeVar endpoint on the wire; producer at the wire's scope) are satisfied naturally by definition wires as built. After fusing the program wire, the zero wire becomes the next producer/consumer pair — fusions chain without preparation.
- `conversion` with a recorded certificate replays fuel-free on the fused pure term; the target `port(a)` (o = a) is the relational form of the old `target: port('s0')` recipes.
- `ProofContext.definitions` is still a required field (`{}` works) — it dies in Task 2.
- Port names inside relation bodies are freshened by the splice; derivation code must locate spliced nodes/wires STRUCTURALLY (by term shape / endpoint pattern), never by name — consistent with the port-name law.

---

### Post-plan: the rest-interval redesign (feel-report physics, final)

The user's live reports (never-settling jitter; cuts inflating around
disconnected content) drove a measured redesign of the relaxation. Refuted by
experiment along the way (each ablated/measured, see commits): θ-channel
drive, min-circle solver wobble as sole cause, support-weighted force routing,
PBD velocity reconciliation, degree-normalized attraction, an unbounded
barrier (created a 2000-unit "sling": it exiled split content faster than the
capped springs could bring it home), and project-to-interval-middle (a
projection storm: inserting wide gaps pairwise re-violates neighbours
forever).

**What landed (the interval-rest architecture):** every standing cycle
observed traced to a POINT equilibrium being re-excited — by breathing of the
derived circle geometry, by field-vs-projection disagreement, or by
unbounded-vs-bounded force mismatches. Rest is now an INTERVAL:

- ONE sibling pair force on the real circle gap: a SATURATED barrier
  (holds realistic crowds of attractions, loses to a bundle of leg springs so
  split content can always come home) below `REST_LO = 2·SIB_GAP`; exactly
  ZERO force through `REST_HI = 4·SIB_GAP`; saturated constant attraction
  beyond. Content coasts into the dead zone and nothing acts on it again.
- Exact minimal enclosing circles (closed-form support refinement) so the
  zone's edges are not chattered by solver noise.
- Projection to the boundary (not the zone middle), every tick.
- All soft forces still share the single SOFT_MAX bound; springs capped.

**Measured outcome:** settling is ~20× faster (full 2600-tick settles run in
0.3–0.5 s in vitest, were 8–12 s); no pops (max single-tick jump 0.1 world
units); most diagrams reach TRUE rest (succShiftS@24 decays to 0.4 u/200t and
stays). Two plusComm double-cut steps (32, 48) and succShiftS@48 are
TOPOLOGICALLY STRAINED — their wiring (legs from deep content to hub
junctions) wants distances their cut-nesting cannot give, so the layout
wanders a near-flat conflicted valley at ~0.05 u/tick (plateaus unchanged
after 10k+ ticks under every field variant; the force-watch shows a permanent
three-way tug: sibling attraction toward a region-mate vs leg springs toward
the hub vs the crowd barrier). The battery asserts TRUE rest where achieved
and explicit REGRESSION BOUNDS (~2× measured plateau, labelled as such — not
rest claims) on the strained trio, pinning against the historical 20–150 u
runaways. Open follow-up if the residual matters visually: full min-circle
differentials (support + shrink terms), so region-level forces can pull split
content home through the circle rather than shoving the circle away.
