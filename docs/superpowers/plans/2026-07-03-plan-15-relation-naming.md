# Plan 15: In-session relation naming — user-defined relations from the live sheet

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** The user can NAME a selection of the live sheet as a new relation — turning a selected subgraph plus an ordered pick of its crossing wires into a `DiagramWithBoundary` registered in the working context — after which the existing machinery does everything else: relFold/relUnfold on the new ref, rendering as a named disc (with the port pip fixing argument order), persistence through Save theory, round-trip through the Library. No new kernel rule: registering a definition is a conservative definitional extension; no diagram changes when a relation is defined.

**Semantics (fixed):**
- A relation definition is the EXTRACTED COPY of the selection (`extractSubgraph` — the same gates comprehension abstraction uses; refusals surface verbatim in the status line). The sheet is not modified by defining.
- Boundary = the selection's crossing wires, ORDERED by the user's picks (the pick order IS the argument order — the same interaction as citation's "click the argument wires in boundary order", and the pip renders that order on the disc). Every crossing wire must be picked exactly once; a partial or duplicated pick refuses with an instructive message.
- Name gates: nonempty; collision with ANY existing relation (loaded or session) refuses loudly ("relation 'x' already exists (loaded from a.json)"); collision with theorem names refused too (one namespace for citable things keeps the fold/cite inputs unambiguous).
- The new relation joins: the live ctx.relations (relFold/relUnfold immediately usable), the shell's persistence record (Save theory serializes it — theoryToJson already carries relations), and the Library's Session group (listed beside adopted theorems, uniformly).

### Task 1: Headless core

**Files:** `src/app/define.ts` (or the existing edit/session module if it fits better — one home, no scattering): `defineRelation(diagram, sel, orderedWires, name, ctx, relations) → { relation: DiagramWithBoundary }` implementing every gate above as loud errors.
**Test:** `tests/app/define.test.ts` — happy path (define, then relFold a fresh copy of the body into the new ref, then relUnfold reproduces it — the round-trip IS the correctness statement); every refusal observed with its message (empty name, name collisions both kinds, missed crossing wire, duplicate pick, non-crossing wire picked, extraction-gate violations pass through verbatim).

- [x] Core + tests green; suite + tsc green. Commit.

**Findings (Task 1):** `src/app/define.ts` + `tests/app/define.test.ts` (11 tests). Two points where the spec's letter met the implementation:
- *"extraction-gate violations pass through verbatim"*: the DiagramError extractSubgraph can throw (atom bound below the anchor) is UNREACHABLE from a valid `mkSelection` — extract.ts:33 documents this. The reachable extraction gate is the OPEN-subgraph case (`binderStubs.length > 0`): an atom bound by a binder that encloses the anchor but sits outside the selection. Comprehension abstraction (comprehension.ts:177) and relFold (reldef.ts:69) both refuse it, and such a body could never be folded, so `defineRelation` refuses it too — that is the gate the test exercises.
- *name-collision message "(loaded from a.json)"*: the pure core receives only `ctx` + the `relations` record, neither of which carries per-file provenance, so the message names the namespace ("relation … already exists (loaded or defined this session)" / "already a theorem") but not the source file. Loud and instructive; provenance would require threading the Library, which the headless core does not take.

### Task 2: Shell wiring + e2e

**Files:** `src/app/shell.ts` — a "Define relation…" action available with a selection in EDIT mode: enters a pending state (same two-phase pattern as cite/relFold: "click the crossing wires in argument order, then Commit"), name read from the existing name input at commit; success registers the relation, updates the Library Session group, and reports "defined 'foo' (arity 2)". Refusals verbatim in the status line.
**Test:** e2e: build a small body on the sheet, select it, define it, fold a second copy into the new ref (the panel's relation appears; the fold works), Save theory → the downloaded/persisted JSON contains the relation; reload through the Library round-trips it.

- [x] Shell + e2e green; full suite + tsc green. Commit.

**Findings (Task 2):**
- *Persistence design*: session-defined relations are first-class in the `Library` (a new `definedRelations` list, parallel to `adopted` theorems) so `rebuild` re-merges them on every library change — mutating `ctx.relations`/`relations` directly would be wiped by the next load/unload. `defineEntry(lib, name, relation)` mirrors `adoptEntry` (rebuild-for-conflict pre-check). `rebuild` layers defined relations into both the `relations` record and `ctx.relations`, checks name collisions across the single relation+theorem namespace (defined-vs-loaded/defined relation, defined-vs-theorem, and adopted-theorem-vs-relation), and re-resolves each defined body's refs (`assertRefsResolve`, now exported from store.ts) so unloading a file a defined relation cited refuses loudly. Save theory needs NO change — the defined relation is already in the `relations` record `sessionTheory` serializes.
- *Shell*: "Define relation…" appears in the EDIT-mode action menu when a selection exists; the pending pick reuses the exact cite/relFold two-phase branch; commit reads the name input, calls `defineRelation` then `defineEntry`→`applyLibrary`, reports `defined 'foo' (arity N)`. Session group renders defined relation names.
- *e2e seam additions (noted per instructions)*: `wires()` returns verified-hittable world points per rendered wire (each confirmed via the real `hitTest` to resolve back to its wire) — the wire analogue of the existing `bodies()` locator, used to click argument wires with real canvas clicks. `theoryJson()` returns the live saveable theory (the seam path the plan sanctions for the Save assertion). No selection was driven through a non-click seam; every select/pick/commit is a real pointer event.
- *Friction surfaced (not a semantic change)*: `onSetLhs` snapshots `editDiagram` by reference, so `session.forward.current === editDiagram` on entering PROVE and `sync()` sees no identity change — the edit selection carries into PROVE. Legitimate app behavior; the e2e deselects+reselects explicitly rather than depend on it.

### Task 3: Review + close

- [ ] Independent adversarial review: name-collision and partial-pick probes; verify defining NEVER mutates the sheet diagram; JSON round-trip of a session-defined relation through loadTheory; the pip renders the defined argument order (paint-level check).
- [ ] Plan-doc + memory sync; close.
