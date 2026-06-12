# Plan 11c: Name-Blind Free Ports (canonicalize at construction)

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Enforce the user's law — free-port names are never semantic and never user-visible. Two diagrams that differ only in free-port naming must be the SAME diagram: equal fingerprints, interchangeable in matching, congruence-joinable with an empty certificate.

**Architecture:** `mkDiagram` gains a canonicalization pass: every term node's free ports are simultaneously renamed to `s0, s1, …` in first-occurrence order, and the freeVar endpoint keys of its wires are rewritten through the same map, before validation. Every rule application already ends in `mkDiagram`, so rules keep their name-based plumbing unchanged — the names become forced (a canonical name IS the position, spelled as a string), so they carry zero information. No API changes in the rules layer; no migration code anywhere (bundled theories rebuild from source; pre-change saved sessions invalidate, which is correct per house rules).

**Why not position-threading:** rewriting `wireAt`/`substPort`/conversion-attachments to positional APIs would touch every rule and serializer for the same end state. Canonical names achieve renaming-invariance at one seam.

**Key properties the implementation must have (and tests must pin):**
- *Determinism + idempotence:* canonicalizing a canonical diagram is the identity. The rename is a SINGLE simultaneous pass (each port leaf looked up once by its original name), so swaps like {s0→s1, s1→s0} are handled without capture or sequencing bugs.
- *Per-node scope:* each node's term canonicalizes independently; atoms and output ports untouched.
- *Endpoint consistency:* a wire endpoint `{node, freeVar n}` is rewritten iff its node's map contains n; an endpoint naming a port absent from the node's term remains for validation to reject exactly as today.
- *The law itself:* construct the same shape twice with different source names → `diagramFingerprint` equal; a `SUCC q` node and a `SUCC y` node wired identically are termEq after construction (congruenceJoin with empty certificate succeeds); deiteration accepts a copy built under different names.

---

### Task 1: renameFreePorts + the canonicalization pass + law tests

**Files:**
- Modify: `src/kernel/term/term.ts` (add `renameFreePorts`)
- Modify: `src/kernel/diagram/diagram.ts` (`mkDiagram` canonicalization pass before validation)
- Test: `tests/kernel/term/term.test.ts` (rename helper), `tests/kernel/diagram/canonical-ports.test.ts` (new — the law battery)

**Step 1 — failing tests first.** `renameFreePorts(t, map)`: simultaneous, single traversal, leaves not in the map unchanged; swap map `{a→b, b→a}` exchanges them; bound vars and constIds untouched. Law battery: (a) two builder-constructed diagrams identical up to free names → equal `diagramFingerprint`; (b) `mkDiagram` output node terms have frees named `s0…` in first-occurrence order and every freeVar endpoint key matches; (c) idempotence — `mkDiagram` of an already-canonical structure is endpoint-identical; (d) the swap case canonicalizes deterministically; (e) a wire endpoint naming a non-existent port still fails validation with today's error; (f) congruenceJoin between two same-shape nodes built under different names, wired to one shared free wire and separate outputs, succeeds with the empty certificate; (g) deiteration: a copy region built with different source names than its justifier still deiterates. Run; observe failures.

**Step 2 — implement.**

```ts
// term.ts — simultaneous free-port rename; single pass, original-name lookup
export function renameFreePorts(t: Term, map: ReadonlyMap<string, string>): Term {
  switch (t.kind) {
    case 'port': {
      const to = map.get(t.name)
      return to === undefined ? t : port(to)
    }
    case 'bvar': case 'const': return t
    case 'lam': return lam(renameFreePorts(t.body, map))
    case 'app': return app(renameFreePorts(t.fn, map), renameFreePorts(t.arg, map))
  }
}
```

```ts
// diagram.ts — inside mkDiagram, before validation:
// per term node: order = freePorts(node.term); map n → `s${i}`; skip if already canonical.
// Rewrite the node's term via renameFreePorts and every freeVar endpoint of that node
// through the same map. Atoms and non-freeVar ports pass through untouched.
```

(Adapt constructor names to the actual Term constructors; keep the pass allocation-light — when every node is already canonical the input objects are reused.)

**Step 3 —** targeted tests pass; then `npx tsc --noEmit`; then the FULL suite — expect fixture fallout; do NOT fix unrelated fixtures in this task (Task 2 owns that), but list the failing files in your report. Commit `plan 11c task 1: canonical free ports at construction (the name-blindness law)` if the new tests + term/diagram suites are green even when theory/rule fixtures still fail; include the fallout list in the commit body.

- [x] Law battery green, term/diagram suites green, tsc clean. Committed `plan 11c task 1: canonical free ports at construction (the name-blindness law)` (b68d7fe, fallout list in commit body).

### Task 2: Fixture and call-site adaptation

**Files:** whatever Task 1's fallout list names — expected concentration: `tests/kernel/rules/fusion.test.ts` (asserts post-fusion names like `y_0`), theory derivations and `src/theories/macros.ts` callers using `wireOf(node, 'freeVar', '<original name>')` after construction, shell/edit tests reading named ports post-build, match/roundtrip fixtures.

Rules of engagement: every fix asserts the CORRECT canonical behavior (never weakened, never skipped). Where a test asserted a specific fresh name (`y_0`), the correct assertion is now structural (the port count, the wiring, termEq against the canonically-named expectation). Where theory code looks up a port by original name post-construction, switch it to the canonical name read from `freePorts(node.term)` at that point (position-stable), or extend `macros.wireOf` to accept a position index — pick per site, no wrappers, no dual paths. The spike scripts under docs/ are historical artifacts pinned to the pre-change kernel: do NOT update them; instead add a one-line README in the spike-scripts directory stating they predate Plan 11c name-blindness (their constructions remain correct; only their literal name bookkeeping is stale).

- [x] Full suite green, tsc clean, `npm run e2e` green. Commit `plan 11c task 2: canonical-port fixture adaptation`. (b87fe2e)

### Task 3: Adversarial review

Mutation probes (each observed fail → revert → pass): (1) skip the endpoint rewrite (canonicalize terms only) — the consistency/law tests must fail; (2) canonicalize by per-DIAGRAM occurrence order instead of per-node — a two-node test must fail; (3) sequential substPort-style rename instead of simultaneous — the swap test must fail; (4) make the pass non-idempotent (always fresh names) — idempotence test must fail. Independent hunt: portKey collisions (`s0` vs a user-typed `s0` in a DIFFERENT position), JSON roundtrip of canonical diagrams, matcher/labeling invariance, view-layer portAnchors keyed by the now-canonical names (geometry must still resolve — run the view tests and one E2E). Verdict + any new pins committed.

- [x] APPROVED verdict recorded; plan-doc sync. (review battery: 6a91ecd)

---

## Execution record (Task 3 adversarial review, 2026-06-12)

**Mutation probes on the canonicalization pass** (each: mutate → observe fail → revert → observe pass; `git diff src/` empty after):

| # | Mutation | Caught by |
|---|----------|-----------|
| 1 | Skip the endpoint rewrite (terms only) | law battery (b), (d), (e)×2, (f), (g), (a) — 7 of 8; plus 30 failures across json/selection/splice/canonical/labeling suites |
| 2 | Per-DIAGRAM occurrence order (shared counter) | law battery (f): two-node termEq fails (second node spelled s1) |
| 3 | Sequential single-name renames | law battery (d): the {s1→s0, s0→s1} swap cascades to `s1 s1` |
| 4 | Non-idempotent (module counter mints t0, t1, … per pass) | law battery (c) idempotence (object identity), plus (b), (d), (f) |

**Fusion share-collapse verdict** (b87fe2e, `residual.has(n) && wa === wb` → wire-keyed map + one simultaneous rename):
- Old condition reconstructed from b68d7fe and OBSERVED by temporary revert: case (i) same wire/different names produced merged term `s0 s1 s2` with TWO freeVar endpoints of the consumer on the shared wire — mkDiagram ACCEPTED it (partition invariant is per-(node,port); a wire may hold several distinct ports of one node). Semantically harmless: both variables ride one wire (one line of identity), so Φ(x,y) ∧ x∼y ≡ Φ(x,x) — sound but redundant. Verdict: NOT unsound; a refusal-in-waiting — fission∘fusion stops being an inverse (fingerprints diverge whenever a shared free is spelled differently on the two nodes, which canonical names make the NORMAL case), so the old gate silently broke equational round-trips, exactly what the new wire-based collapse restores. Cases (ii) same name/different wires (freshen) and (iii) same name/same wire (collapse) are behaviorally unchanged.
- Simultaneity attacked: sequential-substPort mutation observed corrupting both the new pure-collapse cascade pin (`(s0 s0) s1 s0` instead of `(s0 s1) s0 s1`) and the existing "migrates" pin; reverted, green.
- New pins committed (6a91ecd): pure-collapse cascade simultaneity; fission position-stability in a multi-free-port term (+ fingerprint inverse); fission∘fusion round-trip where the shared individual is spelled s0/s1 on the two nodes — ONE endpoint on the shared wire, variable used in BOTH positions.
- fission `freshPortName(_, 'q')`: 'q' never collides with canonical s-names; mkDiagram immediately re-canonicalizes it. headstrip mints no port names (freshId for node/wire ids only) and already corresponds heads/triviality by WIRE, not name.
- joinPorts: requiredPorts pre-check verified to run before the wire scan; for any mkDiagram-produced diagram a port passing the pre-check is attached to exactly one wire (partition invariant), so the "no wire holds" branch is unreachable for valid inputs and remains a loud guard against structurally-typed forgeries.

**Sweep:** JSON roundtrip green (json.test.ts, canonical terms asserted); loadTheory canonicalization pinned (hand-crafted v:y/v:z file loads as v:s0/v:s1 — new test in store.test.ts); view portAnchors self-consistent (geometry derived from the node's CURRENT canonical term via trompGrid; tromp rail-name tests are term-level, correct layer); view tests 33/33, e2e 3/3 observed. Grep sweep over `freeVar', name:` literals: all non-canonical spellings in src/ and tests are pre-build builder wires (rewritten by mkDiagram), pure-JSON step serialization data, term-level APIs, or rejection pins; the only out-of-order s-name construction is the deliberate swap test (d). No lookup survives by luck.

**Final:** 600 tests passed (596 + 4 review pins), tsc clean, e2e 3/3. `git diff src/` empty. **VERDICT: APPROVED.**
