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

- [ ] All theorems restated per rubric (or flagged with reasons), batteries green, suite + tsc + e2e green. Commit.

### Task 3: Review + close

- [ ] Independent adversarial review: slot-order mutation probes (swap two slots → order test fails; drop the pip → paint test fails; revert the aim to radial → the slip-past test must fail — construct it); statement probes (restated theorems' rhs pins are real: a trivialized rhs must fail checkTheorem or the pin); replay + physics sentinels.
- [ ] Plan-doc + memory sync; close.
