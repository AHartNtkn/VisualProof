# Plan 18: Canonical boundary slots + natural theorem statements

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Two user reports (2026-07-03):**
1. **BUG — boundary exits have no canonical order and slip past each other.** The boundary IS ordered data (theorem statements fix the wire order) but exits render wherever each anchor's radial crosses the frame. Consequence stated by the user: "there's no way to distinguish the left hand side and the right hand side of the plusComm theorem" — the crossing is the theorem, and the drawing hides it. Same semantic-honesty family as rendering law 4.
2. **Awkward statements throughout frege.ts.** User's exemplar: zeroIsNat "binds a free variable and asserts that that variable being zero is the same as it being zero and a natural number… an extraordinarily awkward way to phrase that theorem." The natural form: NO boundary at all — "you just connect zero to Nat and then do the manipulations until you're left with a blank page" (backwards reading; forward: empty sheet ⟹ ∃z. Zero(z) ∧ nat(z)).

### Task 1: Canonical boundary slots (the bug)

**Design — the frame is the sheet's node:** extend the pip convention. The frame carries a pip marking boundary position 0; the n boundary wires get FIXED perimeter slots in boundary order, clockwise from the pip (slots distributed evenly around the rounded-rect perimeter by arc length). The drawn exit for boundary wire i terminates at slot i — always; exits structurally cannot swap. The relax boundary-exit aim targets the body's OWN slot (a fixed frame-relative point) instead of the outward radial — the layout organizes to meet its slots, and a fixed target is better-behaved than any position-derived aim (no chase, no flips). The pip on the frame uses the same device-pixel dot vocabulary as disc pips (arity ≥ 2... for the frame, show the pip whenever ≥ 2 boundary wires; a 0/1-boundary sheet needs no mark).

**Files:** `src/view/wires.ts` (boundaryExits: slot placement by perimeter arc-length parameterization of the rounded rect, exit tangent = frame normal at the slot), `src/view/relax.ts` (the boundary aim targets slot i), `src/view/paint.ts` (frame pip dot at slot-0's perimeter position), `src/view/engine.ts` if slot geometry helpers belong there.
**Test:** exits are order-faithful (for a 3-boundary diagram, the perimeter order of exit points equals the boundary order, clockwise from the pip — sweep the layout by moving bodies; the slot assignment NEVER changes); the corner-continuity test survives (slots are fixed, so continuity is trivial — keep the sweep as a regression); paint-level frame-pip test (≥2 boundary → exactly one pip dot at slot 0; ≤1 → none); the plusComm acid test: render lhs and rhs of the bundled plusComm — their canonical DRAWN forms must differ (the crossing is visible: assert the wire→disc-port correspondence read from the two sides' display lists differs). Physics battery stays green (the aim change must not regress the at-rest results — rerun the strained-case bounds).

- [x] Slots + pip + aim + tests green; suite + tsc + e2e green. Commit.

**Findings (Task 1, done):**
- Slot geometry lives in `engine.ts` as `frameSlots(fb, n)`: n points spaced evenly by arc length around the frame's rounded rect, slot 0 at the top-edge midpoint (the pip origin), clockwise (canvas y-down). `normal` is the exact outward frame normal (axis-aligned on edges, radial on corners) — analytic, so exits ride the drawn line without the old bisection/SDF machinery. The ray-cast `frameSdf` in `wires.ts` is deleted (was dead once slots are fixed).
- `boundaryExits` (wires.ts) and the boundary aim (relax.ts) both target slot i for boundary index i, read from the same `frameSlots`, so the relaxed aim and the drawn exit coincide exactly (no chase). Junction boundary bodies keep their exits (aimed by trunk geometry); relax skips their port-normal aim as before.
- Frame pip: device-pixel dot (PIP_R family, ink stroke) at slot 0, drawn only when `e.boundary.length >= 2`.
- plusComm acid test (directly observed): lhs and rhs draw slot 0/1/2 at the SAME fixed perimeter points (top ~y-42, right ~x45, lower-left ~x-33) but slot→plus-arg wiring differs — lhs [0,1,2], rhs [1,0,2]. Slots 0 and 1 cross; the crossing is now visible instead of hidden by position-derived exits.
- **Strained trio, before (radial aim) → after (fixed-slot aim), max drift over 200 post-settle ticks (bound):** plusComm@20 3.474 → 3.104 (bound 6); succShiftS@24 0.433 → 0.364 (bound 2); succShiftS@48 9.212 → 8.955 (bound 12). Fixed slots slightly IMPROVE all three; no bound tightened.
- Tests: `frameSlots` geometry (engine.test.ts); order-faithfulness under a 6-layout wild sweep + plusComm acid test (wires.test.ts); frame-pip present/absent (paint.test.ts); corner-continuity sweep kept as regression. Suite 885/885, tsc clean, e2e 8/8.

### Task 2: Natural theorem statements (the restatement pass)

**Direction (user):** every theorem in frege.ts (and lambda.ts) is audited for its MOST NATURAL statement. The rubric:
- Standalone facts become CLOSED sentences (boundary []): `zeroIsNat`: empty sheet ⟹ ∃z. Zero(z) ∧ nat(z). `oneIsNat`: empty sheet ⟹ ∃z,s. Zero(z) ∧ Succ(z,s) ∧ nat(s). Backwards reading = manipulate to the blank page.
- Rule-shaped theorems that are CITED WITH ARGUMENTS keep boundary (sequent) form — that is what lets a citation rewrite in place: `plusComm`, `succShiftS`, and the units if they are cited as rewrites. But their statements are still audited for gratuitous repetition (e.g., hypotheses repeated on the rhs merely because the derivation kept them — restate to the clean form and adjust the derivation, e.g. via erasure at the appropriate polarity, rather than shipping the artifact).
- `succNat`: judgment call — conditional by nature; the closed form ¬∃n,s[nat(n) ∧ Succ(n,s) ∧ ¬nat(s)] vs the sequent form. Choose what composes: oneIsNat's derivation and the nat(1)-certification smoke test must still work (citing a closed sentence = inserting the proven sentence at a positive region and joining; verify this road actually works in the current kernel before committing to closed form — if it does not compose, keep succNat rule-shaped and SAY SO in the findings).
- Consumers must keep working: plusComm still cites succShiftS; the smoke test still certifies nat(1) and cites plusComm against it (adapt the smoke test to the new statement forms — the CONTENT of the check, "a concrete numeral satisfies the guarded arithmetic", must survive verbatim).

**Files:** `src/theories/frege.ts` (restatements + re-derivations), `src/theories/lambda.ts` (same audit), batteries updated to the new statements (the no-const guard, statement-adequacy pins, and JSON round-trips all retarget).
**Test:** every restated theorem checkTheorem-green through the JSON road; statement-adequacy pins updated to pin the NEW forms (closed sentences: assert boundary [] and the rhs canonical form; the crossing pin for plusComm survives); e2e replay retargets if step counts shift.

- [x] All theorems restated per rubric (or flagged with reasons), batteries green, suite + tsc + e2e green. Commit.

**Findings (Task 2, done):**

Statement table (old → new). Only two theorems changed form; the rest are recorded with the reason they keep their shape.

| theorem | old statement (boundary) | new statement (boundary) | verdict |
| --- | --- | --- | --- |
| zeroIsNat | `Zero(z) ⟹ nat(z) ∧ Zero(z)` (1) | `⟹ ∃z. Zero(z) ∧ nat(z)` (0, CLOSED) | **restated** — standalone fact |
| oneIsNat | `Zero(z) ∧ Succ(z,o) ⟹ nat(o) ∧ Zero(z) ∧ Succ(z,o)` (2) | `⟹ ∃z,s. Zero(z) ∧ Succ(z,s) ∧ nat(s)` (0, CLOSED) | **restated** — standalone fact |
| succNat | `nat(n) ∧ Succ(n,s) ⟹ Succ(n,s) ∧ nat(s)` (2) | *unchanged* | kept rule-shaped (see verdict) |
| plusComm | `ℕ(a) ∧ ℕ(b) ∧ Plus(a,b,o) ⟹ ℕ(a) ∧ ℕ(b) ∧ Plus(b,a,o)` (3) | *unchanged* | kept sequent — cited with args by the smoke test |
| succShiftS | `ℕ(a) ∧ Succ(b,sb) ∧ Plus(a,sb,o) ⟹ ℕ(a) ∧ Plus(a,b,t) ∧ Succ(t,o)` (3) | *unchanged* | kept sequent — cited by plusComm |
| plusAssoc | `Plus(a,b,t) ∧ Plus(t,c,o) ⟹ Plus(b,c,u) ∧ Plus(a,u,o)` (4) | *unchanged* | universal rewrite (free a,b,c) — inherently open |
| plusLeftUnit | `Zero(z) ∧ Plus(z,a,o) ⟹ o = a` (2) | *unchanged* | universal identity (free a) — inherently open |
| plusRightUnit | `Zero(z) ∧ Plus(a,z,o) ⟹ o = a` (2) | *unchanged* | universal identity (free a) — inherently open |
| lambda onePlusOne | `o = (PLUS ONE ONE) ⟹ o = TWO` (1) | *unchanged* | computation rewrite, cited with args in battery.test |
| lambda fixedPoint | `o = Y f ⟹ o = f (Y f)` (2) | *unchanged* | Y-unfolding rewrite, cited with args |

- **zeroIsNat (closed):** empty lhs; the zero witness is minted by `closedTermIntro ZEROp` on a fresh existential z-line (replacing the old boundary hypothesis + its `relUnfold`). Everything else — guard bubble, base+closure insertion, the endpointTransport of the conclusion atom onto the z-line — is unchanged. rhs is `∃z. nat(z) ∧ Zero(z)`, boundary []. Steps 12 (was 12: gained the intro, lost the external-zero unfold).
- **oneIsNat (closed):** empty lhs. Cites the closed zeroIsNat (empty-selection insertion) to plant `Zero(z) ∧ nat(z)`, mints `Succ(z,s)` on the z-line (K-trick a `SUCC z` node off a spent ZEROp seed, then `refoldSucc`), then cites the **rule-shaped** succNat forward on `nat(z) ∧ Succ(z,s)` to reach `nat(s)`. rhs `∃z,s. Zero(z) ∧ Succ(z,s) ∧ nat(s)`, boundary []. Steps 9 (was 2).
- **succNat composability verdict — kept rule-shaped.** A closed-sentence succNat would be `¬∃n,s[nat(n) ∧ Succ(n,s) ∧ ¬nat(s)]`. Spiked (observed, not theorized): a closed theorem is `boundary []`, so `applyTheorem` forces `at.args = []` — a citation can only INSERT the whole proven sentence; it carries no argument wires to bind onto the host's own n,s lines. Directly observed with the now-closed oneIsNat: `applyTheorem` with host args `[wz,wo]` is REJECTED ("selection is not an occurrence of oneIsNat lhs"); only empty-selection insertion is accepted, which plants a fresh certified 1 disconnected from any host line. To then extract `nat(s)` for a concrete host `s` from an inserted `¬∃n,s[...]` you must identify the ∃-bound n,s with the host's z,s (deiteration needs the copies already joined) — i.e. join a bubble-scoped line to a root line, the scope wall these theorems fight (endpointTransport only sidesteps it for equal CLOSED values, which a general n,s is not). So the closed road does NOT compose in the current kernel. The rule-shaped succNat, by contrast, matches the occurrence's lines by the boundary-pinned check and rewrites in place — exactly what oneIsNat needs. oneIsNat + the smoke test both verify against it end-to-end.
- **plusComm / succShiftS audit (no gratuitous artifacts):** the repeated ℕ-guards on both sides are soundness preconditions retained for chaining, not derivation residue — dropping them from the rhs would state a different (unsound-to-chain) rule. succNat's retained `Succ(n,s)` on its rhs is likewise load-bearing (it is exactly the `Succ(z,s) ∧ nat(s)` oneIsNat consumes). Left as-is.
- **Units / assoc / lambda:** all are universally-quantified rewrites over free boundary parameters (0+a, a+0, (a+b)+c, PLUS ONE ONE, Y f). A closed form would have to bind those parameters, which is not their meaning; the natural statement IS the open rule. Nothing cites the units/assoc, but the rubric's "otherwise judge by the rubric" resolves them to sequent form. onePlusOne is demonstrably cited with args (battery.test), confirming the rule shape.
- **Batteries retargeted alongside each restatement:** frege.test.ts zeroIsNat/oneIsNat pins now assert boundary [], empty lhs, and existential (root-scoped, non-boundary) z/s lines; the smoke test now INSERTS the closed oneIsNat, builds `nat(b) ∧ Plus(s,b,sum)` around the certified 1-line, and cites plusComm — the crossing assertion (`Plus` reads `(b,s,sum)`) survives verbatim. succNat/plusComm/succShiftS/units/assoc pins unchanged. battery.test.ts, macros.test.ts, lambda.test.ts unchanged (names and counts stable). transport.test.ts:231's descriptive comment about zeroIsNat's nested-cut conclusion atom stays accurate (the transport structure is unchanged).
- **Validation:** `tsc --noEmit` clean; `vitest run` 885/885; `npm run e2e` 8/8 (plusComm still last, 64 steps, boundary 3 — the replay spec needed no retarget). JSON round-trip (`theoryToJson → loadTheory`) re-verifies both closed theorems via checkTheorem.

### Task 3: Review + close

- [ ] Independent adversarial review: slot-order mutation probes (swap two slots → order test fails; drop the pip → paint test fails; revert the aim to radial → the slip-past test must fail — construct it); statement probes (restated theorems' rhs pins are real: a trivialized rhs must fail checkTheorem or the pin); replay + physics sentinels.
- [ ] Plan-doc + memory sync; close.
