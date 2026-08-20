# TypeScript Kernel Soundness Fixes Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Close the four soundness holes the 2026-08-20 Lean↔TS audit found in the TypeScript kernel (cutWrap, uniform argDrop, sever above scope, boundary-wire rebinding during theorem replay) and two correctness defects found alongside them (wireJoin inversion, swallowed error in deiteration search).

**Architecture:** Every fix follows the kernel-wide invariant of the derived-scope spec §5: an incidence-changing rule either provably preserves every surviving wire's derived scope, refuses with `ScopePreservationError` ("pin first"), or deposits a pin at the old scope. Rules keep operating on closed diagrams; the one proof-layer fix (theorem replay) enforces what the Lean calculus enforces by typing — a boundary wire is never a local binder, so no rule may rebind it.

**Tech Stack:** TypeScript, vitest (`npx vitest run --config vitest.config.ts <file>`), `npx tsc --noEmit -p tsconfig.json`.

**Spec:** `docs/superpowers/specs/2026-08-12-derived-scope-identity-rules-design.md` §5 ("Obligations on every other rule"). The audit findings are recorded in the coordinator's report (this plan restates each as a failing test).

## Global Constraints

- Repo root: `/home/ahart/Documents/VisualProofAssistant/.worktrees/signature-indexed-wires`. Branch `worktree-signature-indexed-wires`.
- Every task: failing test first, observe it fail, fix, observe it pass, run `npx tsc --noEmit -p tsconfig.json` (expect 0 errors), commit with `git add <specific files>` only. Never `git add -A`.
- Do not touch `VisualProof/` (Lean) — another agent owns it. Do not touch the uncommitted `VisualProof/Audit.lean` modification.
- No `catch {}` / `|| true` / silent skips. No "legacy"/"compat" code. No TODOs.
- Commit trailer on every commit:
  ```
  Co-Authored-By: Claude Fable 5 <noreply@anthropic.com>
  Claude-Session: https://claude.ai/code/session_01HJcUfnQFi96MNqW9LuHdn9
  ```
- Test files use the repo's existing helpers: `DiagramBuilder` (`src/kernel/diagram/builder.ts`: `.root`, `.cut(parent)`, `.atom(region, sig)`, `.wire(endpoints, sig)` returning the wire id, `.pin(wire, region)` returning the pin node id, `.build()`, `.buildOpen(boundary)`), `derivedScope`/`polarity` from `src/kernel/diagram/regions.ts`, `IOTA`/`relSig` from `src/kernel/diagram/sig.ts`.

---

### Task 1: cutWrap must not move argument-wire quantifiers

**Files:**
- Modify: `src/kernel/rules/wire-ends.ts` (add `pinMovedQuantifiers` next to `completeWireEnds`, ~line 247)
- Modify: `src/kernel/rules/wire-content.ts:57-100` (`applyCutWrap`)
- Modify: `src/kernel/rules/doublecut.ts:31-73` (`applyDoubleCutIntro` — reuse the helper)
- Test: `tests/kernel/rules/scope-preservation.test.ts`

**Interfaces:**
- Produces: `export function pinMovedQuantifiers(before: Diagram, parts: PartsInProgress, wireIds: Iterable<WireId>, reservation?: IdNamespaceReservation): void` in `wire-ends.ts`. For each wire id that still exists in `parts.wires`, if `endpointDca(parts, wire.endpoints)` differs from `derivedScope(before, wireId)`, append one arity-1 identity node (a pin) at the old scope to that wire. Idempotent on wires whose DCA did not change.

Why: `applyCutWrap` deletes each end atom and re-attaches its argument wires to a fresh atom inside a fresh cut under the end's region. An argument wire whose every incidence sat on wrapped atoms now has all incidences one cut deeper, so its derived scope (its existential quantifier) silently sinks into the new cut. Semantics: `∃R∃w∃u. R(w,w) ∧ ¬R(u,u)` (satisfiable) becomes `∃W'∃u. ¬∃w.W'(w,w) ∧ W'(u,u)` (unsatisfiable). Lean's `CutShape` keeps every retained wire at its binder. The spec §5 row for cutWrap analysed only the acted wire's successor and missed argument wires; the row's own invariant (every surviving wire's derived scope preserved) is the rule.

- [ ] **Step 1: Write the failing test**

Append to `tests/kernel/rules/scope-preservation.test.ts` (add `import { applyCutWrap } from '../../../src/kernel/rules/wire-content'` — `applyEndsDelete` is already imported from that module; merge the import):

```ts
describe('cut wrap keeps argument quantifiers where they were', () => {
  /** R(w,w) on the sheet and ¬R(u,u); w's only incidences are on the sheet atom. */
  function wrapFixture(): { d: Diagram; R: WireId; w: WireId } {
    const BINARY = relSig([IOTA, IOTA])
    const b = new DiagramBuilder()
    const cut = b.cut(b.root)
    const a = b.atom(b.root, BINARY)
    const c = b.atom(cut, BINARY)
    const R = b.wire([{ node: a, port: { kind: 'head' } }, { node: c, port: { kind: 'head' } }], BINARY)
    const w = b.wire([
      { node: a, port: { kind: 'arg', index: 0 } },
      { node: a, port: { kind: 'arg', index: 1 } },
    ])
    const u = b.wire([
      { node: c, port: { kind: 'arg', index: 0 } },
      { node: c, port: { kind: 'arg', index: 1 } },
    ])
    b.pin(u, b.root)
    return { d: b.build(), R, w }
  }

  it('pins an argument wire whose every incidence moves into a new cut', () => {
    const { d, R, w } = wrapFixture()
    const root = d.root
    expect(derivedScope(d, w)).toBe(root)
    const out = applyCutWrap(d, R)
    // BUG: without the cap, w's incidences all sit inside the fresh cut and
    // ∃w sinks under a negation — a satisfiable diagram becomes unsatisfiable.
    expect(derivedScope(out, w)).toBe(root)
    const pins = out.wires[w]!.endpoints.filter((ep) => {
      const node = out.nodes[ep.node]!
      return node.kind === 'identity' && node.arity === 1 && node.region === root
    })
    expect(pins).toHaveLength(1)
  })

  it('adds nothing for an argument wire that keeps an incidence outside the wrap', () => {
    const { d, R, w } = wrapFixture()
    const out = applyCutWrap(d, R)
    // u is pinned on the sheet already: scope unchanged, no second pin.
    const u = Object.keys(out.wires).find((id) => id !== w && out.wires[id]!.sig.kind === 'iota')!
    expect(derivedScope(out, u)).toBe(d.root)
    const pinCount = out.wires[u]!.endpoints.filter((ep) => {
      const node = out.nodes[ep.node]!
      return node.kind === 'identity' && node.arity === 1
    }).length
    expect(pinCount).toBe(1)
  })
})
```

Add the needed imports at the top of the file: `import { DiagramBuilder } from '../../../src/kernel/diagram/builder'` and `WireId` to the type import from `diagram`.

- [ ] **Step 2: Run test to verify it fails**

Run: `npx vitest run --config vitest.config.ts tests/kernel/rules/scope-preservation.test.ts -t "cut wrap"`
Expected: first test FAILS with `expected 'cw' to be 'r0'` (or whatever the fresh cut id is); second passes.

- [ ] **Step 3: Add the helper to `wire-ends.ts`**

Insert after `completeWireEnds` (after line ~245):

```ts
/**
 * Class-(c) scope transport (spec §5): any listed wire whose incidence DCA the
 * rebuild moved receives one pin at its OLD derived scope, so the quantifier
 * stays exactly where it was. Wires whose DCA did not move get nothing.
 */
export function pinMovedQuantifiers(
  before: Diagram,
  parts: PartsInProgress,
  wireIds: Iterable<WireId>,
  reservation?: IdNamespaceReservation,
): void {
  const taken = new Set(Object.keys(parts.nodes))
  for (const wireId of new Set(wireIds)) {
    const wire = parts.wires[wireId]
    if (wire === undefined) continue
    const oldScope = derivedScope(before, wireId)
    if (endpointDca(parts, wire.endpoints) === oldScope) continue
    const node = freshId(taken, 'pin', reservation)
    taken.add(node)
    parts.nodes[node] = { kind: 'identity', region: oldScope, sig: wire.sig, arity: 1 }
    parts.wires[wireId] = {
      sig: wire.sig,
      endpoints: [...wire.endpoints, { node, port: { kind: 'identity', index: 0 } }],
    }
  }
}
```

(`derivedScope`, `endpointDca`, `freshId`, `IdNamespaceReservation`, `PartsInProgress` are already imported/defined in `wire-ends.ts`; check the import list and add `derivedScope` from `'../diagram/regions'` if absent.)

- [ ] **Step 4: Use it in `applyCutWrap`**

In `src/kernel/rules/wire-content.ts`, replace lines 96-99:

```ts
  const parts: PartsInProgress = { regions, nodes, wires }
  transferPins(parts, pins, fresh)
  completeWireEnds(parts, fresh, oldScope, 'cut wrap', reservation?.nodes)
  // The wrapped atoms' argument wires moved one cut deeper with them; any
  // whose quantifier that would drag along is held at its old scope.
  pinMovedQuantifiers(diagram, parts, ends.flatMap((end) => end.args), reservation?.nodes)
  return mkDiagram({ root: diagram.root, ...parts })
```

Add `pinMovedQuantifiers` to the `./wire-ends` import list.

- [ ] **Step 5: Run the test, expect PASS**

Run: `npx vitest run --config vitest.config.ts tests/kernel/rules/scope-preservation.test.ts -t "cut wrap"`
Expected: both PASS.

- [ ] **Step 6: Reuse the helper in `applyDoubleCutIntro` (DRY)**

In `src/kernel/rules/doublecut.ts`, replace lines 56-72 (the `for (const [wireId, wire] of Object.entries(d.wires)) { ... }` loop that pins wires whose DCA changed) with:

```ts
  const parts: PartsInProgress = { regions, nodes, wires: { ...d.wires } }
  pinMovedQuantifiers(d, parts, Object.keys(d.wires), reservation?.nodes)
  return mkDiagram({ root: d.root, ...parts })
```

Change the import on line 7 to `import { pinMovedQuantifiers, type PartsInProgress } from './wire-ends'` and remove the now-unused `endpointDca`, `freshId`, `Endpoint`, `derivedScope` imports if nothing else in the file uses them (check with `npx tsc --noEmit -p tsconfig.json`; unused imports are errors under this repo's config only if `noUnusedLocals` is on — remove them regardless).

- [ ] **Step 7: Run the full kernel tests and tsc**

Run: `npx vitest run --config vitest.config.ts tests/kernel && npx tsc --noEmit -p tsconfig.json`
Expected: all pass, 0 errors. (`tests/kernel/rules/scope-preservation.test.ts` "double cut and quantifier positions" must still pass — it pins the same cases.)

- [ ] **Step 8: Commit**

```bash
git add src/kernel/rules/wire-ends.ts src/kernel/rules/wire-content.ts src/kernel/rules/doublecut.ts tests/kernel/rules/scope-preservation.test.ts
git commit -m "fix(kernel): cut wrap holds argument quantifiers at their old scope

cutWrap moved every wrapped atom's argument wires one cut deeper; a wire
with no other incidence had its existential sink under the new negation
(satisfiable → unsatisfiable). Cap such wires with a pin at the old derived
scope, the same scope transport double-cut intro already performs; the two
rules now share pinMovedQuantifiers."
```

---

### Task 2: argDrop must preserve the dropped attachment wire's scope

**Files:**
- Modify: `src/kernel/rules/wire-args.ts:337-386` (`applyArgDrop`)
- Test: `tests/kernel/rules/wire-args.test.ts`

Why: `applyArgDrop` exempts from the scope check any attachment wire that is "kept elsewhere" (attached at another position of some end). That exemption only guarantees the wire survives, not that its incidence *regions* survive. With the ungated uniform path (all ends share one attachment visible at the acted wire's scope) this fires at positive polarity: `∃R∃p∃q. R(p,q) ∧ ¬R(p,p)` (satisfiable; p's sheet incidence is on R(p,q) position 0) drops to `∃R'∃q. R'(q) ∧ ¬∃p.R'(p)` (unsatisfiable). Lean's `UniformDrops` keeps `p` bound at the sheet. The exemption existed because `requireRemovalScopePreserved` counts every end node as removed and cannot see the rebuilt endpoints; the exact check is: compute the result, then compare each dropped-position wire's derived scope before and after.

- [ ] **Step 1: Write the failing test**

Append to `tests/kernel/rules/wire-args.test.ts` (check its existing imports; it already imports `applyArgDrop`, `DiagramBuilder`, `IOTA`, `relSig`, `derivedScope` — add any missing ones, and `ScopePreservationError` from `'../../../src/kernel/rules/wire-ends'`):

```ts
describe('argument drop keeps the dropped attachment quantifier in place', () => {
  /** R(p,q) on the sheet, ¬(R(p,p) ∧ pin p): p reads at the sheet only through the first end. */
  function dropFixture() {
    const BINARY = relSig([IOTA, IOTA])
    const b = new DiagramBuilder()
    const cut = b.cut(b.root)
    const a = b.atom(b.root, BINARY)
    const c = b.atom(cut, BINARY)
    const R = b.wire([{ node: a, port: { kind: 'head' } }, { node: c, port: { kind: 'head' } }], BINARY)
    const p = b.wire([
      { node: a, port: { kind: 'arg', index: 0 } },
      { node: c, port: { kind: 'arg', index: 0 } },
      { node: c, port: { kind: 'arg', index: 1 } },
    ])
    b.pin(p, cut)
    const q = b.wire([{ node: a, port: { kind: 'arg', index: 1 } }])
    b.pin(q, b.root)
    return { d: b.build(), R, p, cut }
  }

  it('refuses the ungated uniform drop that would sink the attachment under a cut', () => {
    const { d, R, p } = dropFixture()
    expect(derivedScope(d, p)).toBe(d.root)
    // BUG: p is "kept elsewhere" (position 1 of the cut end) and was exempt
    // from the scope check, so the drop went through and ∃p moved into the cut.
    expect(() => applyArgDrop(d, R, 0)).toThrow(ScopePreservationError)
  })

  it('accepts the drop once the attachment is pinned at its scope', () => {
    const { d, R, p } = dropFixture()
    const held = applyVacuityInsert(d, {
      kind: 'pin', wire: p, node: 'hold_p', region: d.root,
    })
    const out = applyArgDrop(held, R, 0)
    expect(derivedScope(out, p)).toBe(d.root)
  })
})
```

(`applyVacuityInsert` from `'../../../src/kernel/rules/identity-rules'`; the pin instance shape is `{ kind: 'pin', wire, node, region }` — see `identity-rules.ts` `VacuityInstance`.)

- [ ] **Step 2: Run test to verify it fails**

Run: `npx vitest run --config vitest.config.ts tests/kernel/rules/wire-args.test.ts -t "dropped attachment"`
Expected: first test FAILS (`expected function to throw`); second passes.

- [ ] **Step 3: Fix `applyArgDrop`**

Replace lines 362-385 of `src/kernel/rules/wire-args.ts` with:

```ts
  // Dropped-position wires lose one endpoint per end: class-(b) — their
  // quantifiers and floors must survive. Wires serving no other position
  // are checked up front with the erasure precondition (actionable
  // "pin first" error); every dropped-position wire is then checked
  // exactly on the rebuilt result, because keeping a wire at another
  // position keeps the wire but not necessarily its incidence regions.
  const dropped = ends.map((end) => end.args[position]!)
  const keptElsewhere = new Set(
    ends.flatMap((end) => end.args.filter((_, index) => index !== position)),
  )
  requireRemovalScopePreserved(
    diagram,
    new Set(ends.map((end) => end.node)),
    new Set([wireId]),
    'dropping an argument',
    new Set(dropped.filter((w) => !keptElsewhere.has(w))),
  )
  const result = replaceEnds(
    diagram,
    wireId,
    ends,
    relSig(sig.args.filter((_, index) => index !== position)),
    (end) => end.args.filter((_, index) => index !== position),
    'drop',
    reservation,
  )
  for (const attachment of new Set(dropped)) {
    if (result.wires[attachment] === undefined) continue
    const before = derivedScope(diagram, attachment)
    const after = derivedScope(result, attachment)
    if (after !== before) {
      throw new ScopePreservationError(
        `dropping an argument would move the quantifier of wire '${attachment}' `
        + `from '${before}' to '${after}'; pin it at '${before}' first`,
        attachment,
        before,
      )
    }
  }
  return result
}
```

Import `ScopePreservationError` from `'./wire-ends'` (it is exported there, line ~300).

- [ ] **Step 4: Run the test, expect PASS**

Run: `npx vitest run --config vitest.config.ts tests/kernel/rules/wire-args.test.ts`
Expected: all PASS.

- [ ] **Step 5: Full kernel tests + tsc**

Run: `npx vitest run --config vitest.config.ts tests/kernel && npx tsc --noEmit -p tsconfig.json`
Expected: green, 0 errors. If a theory/replay test fails because a recorded proof relied on the exemption, that proof was unsound in the case the test covers only if the scope actually moved; inspect the failure, and if it is a scope move, the recorded proof must be re-derived with a pin step (report it — do not weaken the check).

- [ ] **Step 6: Commit**

```bash
git add src/kernel/rules/wire-args.ts tests/kernel/rules/wire-args.test.ts
git commit -m "fix(kernel): argument drop checks the dropped attachment's scope exactly

The kept-elsewhere exemption let an attachment wire survive with all its
remaining incidences under a cut, sinking its existential (unsound on the
ungated uniform path at positive polarity). Check every dropped-position
wire's derived scope on the rebuilt result and refuse with pin-first."
```

---

### Task 3: sever may not lift the fresh wire above the severed wire's scope

**Files:**
- Modify: `src/kernel/rules/wire-quantifier.ts:55-76` (`applyWireSever`)
- Test: `tests/kernel/rules/wire-quantifier.test.ts`

Why: the gate is evaluated at `freshScope`, and `freshScope` is only required to enclose the moved endpoints — nothing ties it to the severed wire's own derived scope. Choosing it above that scope moves an existential above everything in between: `∀x φ(x,x)` (x scoped in a negative cut) becomes `∃y ∀x φ(x,y)`. Lean's `Local.sever` binds the new wire in the region where the rule is applied, which is at-or-below the severed wire's binder. The spec §5 row ("scope above the moved DCA") covers scopes between the moved DCA and the wire's scope, never above the wire's scope.

- [ ] **Step 1: Write the failing test**

Append to `tests/kernel/rules/wire-quantifier.test.ts` (check imports: needs `DiagramBuilder`, `IOTA`, `relSig`, `applyWireSever`, `derivedScope`, `RuleError` from `'../../../src/kernel/rules/error'`):

```ts
describe('sever scope is bounded by the severed wire\'s scope', () => {
  /**
   * ¬[r1: ∃x pin(x) ¬[r2: ¬[r3: P(x) ¬[r4: P(x)]] ¬[r5: P(x) ¬[r6: P(x)]]]]
   *   = ∀x ((Px → Px) ∧ (Px → Px)); x is scoped at r1 (negative).
   */
  function forallFixture() {
    const P = relSig([IOTA])
    const b = new DiagramBuilder()
    const r1 = b.cut(b.root)
    const r2 = b.cut(r1)
    const r3 = b.cut(r2)
    const r4 = b.cut(r3)
    const r5 = b.cut(r2)
    const r6 = b.cut(r5)
    const p3 = b.atom(r3, P)
    const p4 = b.atom(r4, P)
    const p5 = b.atom(r5, P)
    const p6 = b.atom(r6, P)
    const head = b.wire([
      { node: p3, port: { kind: 'head' } }, { node: p4, port: { kind: 'head' } },
      { node: p5, port: { kind: 'head' } }, { node: p6, port: { kind: 'head' } },
    ], P)
    void head
    const arg = (node: string) => ({ node, port: { kind: 'arg', index: 0 } as const })
    const x = b.wire([arg(p3), arg(p4), arg(p5), arg(p6)])
    const pin = b.pin(x, r1)
    return { d: b.build(), x, r1, keep: [arg(p3), arg(p6), { node: pin, port: { kind: 'identity', index: 0 } as const }] }
  }

  it('refuses a fresh scope strictly above the wire\'s derived scope', () => {
    const { d, x, r1, keep } = forallFixture()
    expect(derivedScope(d, x)).toBe(r1)
    // BUG: the gate looked only at the fresh scope (the sheet, positive) and
    // accepted ∀x φ(x,x) → ∃y ∀x φ(x,y).
    expect(() => applyWireSever(d, { wire: x, keep, scope: d.root })).toThrow(RuleError)
    expect(() => applyWireSever(d, { wire: x, keep, scope: d.root })).toThrow(/does not lie within/)
  })

  it('still accepts a fresh scope at or below the wire\'s scope (gated there)', () => {
    const { d, x, r1, keep } = forallFixture()
    // r1 is negative: forward sever refused by polarity, backward accepted.
    expect(() => applyWireSever(d, { wire: x, keep, scope: r1 })).toThrow(/requires a positive scope/)
    const out = applyWireSever(d, { wire: x, keep, scope: r1 }, 'backward')
    expect(derivedScope(out, x)).toBe(r1)
  })
})
```

- [ ] **Step 2: Run test to verify it fails**

Run: `npx vitest run --config vitest.config.ts tests/kernel/rules/wire-quantifier.test.ts -t "bounded"`
Expected: first test FAILS (`expected function to throw`).

- [ ] **Step 3: Add the precondition**

In `src/kernel/rules/wire-quantifier.ts`, after line 65 (`if (d.regions[freshScope] === undefined) { ... }`), insert:

```ts
  // The fresh wire is a new binder at-or-below the severed wire's own binder
  // (Lean: the new local lives in the region the rule is applied in). A
  // scope above it would hoist an existential over every intervening
  // quantifier and cut.
  if (!isAncestorOrEqual(d, oldScope, freshScope)) {
    throw new RuleError(
      `fresh wire scope '${freshScope}' does not lie within the scope `
      + `'${oldScope}' of wire '${input.wire}'`,
    )
  }
```

`isAncestorOrEqual` is already imported in this file (used at line 90).

- [ ] **Step 4: Run the test, expect PASS**

Run: `npx vitest run --config vitest.config.ts tests/kernel/rules/wire-quantifier.test.ts`
Expected: all PASS.

- [ ] **Step 5: Update the doc comment and spec row**

In `src/kernel/rules/wire-quantifier.ts:16-22` change "the fresh wire's scope may be chosen anywhere enclosing the moved endpoints" to "the fresh wire's scope may be chosen anywhere between the moved endpoints' DCA and the severed wire's own derived scope (inclusive)". In `docs/superpowers/specs/2026-08-12-derived-scope-identity-rules-design.md`, the `wireSever` row of the §5 table: append the sentence "The chosen scope must lie at-or-below the severed wire's derived scope; above it the step would hoist the new existential over intervening quantifiers (2026-08-20 audit)."

- [ ] **Step 6: Full kernel + theories tests, tsc**

Run: `npx vitest run --config vitest.config.ts && npx tsc --noEmit -p tsconfig.json`
Expected: green. (Producers never pass a scope above the wire: `src/app/interact/moves.ts` omits `scope`; `compile-content.ts` `invertStep` passes the dying wire's scope.)

- [ ] **Step 7: Commit**

```bash
git add src/kernel/rules/wire-quantifier.ts tests/kernel/rules/wire-quantifier.test.ts docs/superpowers/specs/2026-08-12-derived-scope-identity-rules-design.md
git commit -m "fix(kernel): sever's fresh scope must lie within the severed wire's scope

Gating on the fresh scope alone let a wire bound in a negative region be
split onto a new wire bound at the sheet: ∀x φ(x,x) → ∃y ∀x φ(x,y)."
```

---

### Task 4: theorem replay must not rebind a boundary wire

**Files:**
- Modify: `src/kernel/proof/step.ts` (add `reboundWires` after the `ProofStep` type, ~line 108)
- Modify: `src/kernel/proof/theorem.ts:81-121` (`checkTheorem`'s `carry`)
- Test: `tests/kernel/proof/theorem.test.ts`

Why: `pinnedForReplay` closes an open side by giving every boundary entry a root pin, so during replay a boundary wire is indistinguishable from a root-scoped existential. `endsSpawn` (forward, positive root) or `endsDelete` (backward) on that wire is then accepted — `∃R.⊤ → ∃R.R()` is fine for an existential — but `checkTheorem` records the result as a theorem over the boundary, i.e. for *free* `R`. `registerTheorem` accepts `⊤ ⊢ R()`, and `applyTheorem` of it derives `∀Q.Q()` from a host equivalent to ⊤. In the Lean calculus every rule that rewrites a wire's applications (the wire primitives, leaf rules, ends) requires that wire to be a *local binder* of the region; an external wire never is. The macro layer must enforce the same: a step that rebinds a wire may not act on a current boundary wire.

- [ ] **Step 1: Write the failing test**

Append to `tests/kernel/proof/theorem.test.ts` (the file already imports `DiagramBuilder`, `relSig`, `registerTheorem`, `EMPTY_PROOF_CONTEXT`, `ProofStep`, `applyTheorem`, `Theorem`; `ProofError` from `'../../../src/kernel/proof/error'`; `mkSelection` from `'../../../src/kernel/diagram/subgraph/selection'`; `singleStepAction` from `'../../../src/kernel/proof/action'`):

```ts
describe('boundary wires are not local binders', () => {
  const PROP = relSig([])

  /** lhs: a bare boundary wire R (pin + frame entry). rhs: R applied once. */
  function topToR(): { lhs: ReturnType<DiagramBuilder['buildOpen']>; rhs: ReturnType<DiagramBuilder['buildOpen']>; lw: string; lpin: string; rw: string } {
    const left = new DiagramBuilder()
    const lw = left.wire([], PROP)
    const lpin = left.pin(lw, left.root)
    const lhs = left.buildOpen([lw])
    const right = new DiagramBuilder()
    const atom = right.atom(right.root, PROP)
    const rw = right.wire([{ node: atom, port: { kind: 'head' } }], PROP)
    const rhs = right.buildOpen([rw])
    return { lhs, rhs, lw, lpin, rw }
  }

  it('rejects a backward ends-delete on the boundary wire', () => {
    const { lhs, rhs, rw } = topToR()
    const thm: Theorem = {
      name: 'topImpliesR', lhs, rhs, actions: [],
      backActions: [singleStepAction('delete R ends', { rule: 'endsDelete', wire: rw })],
    }
    // BUG: accepted — certifies ⊤ ⊢ R() with R free.
    expect(() => registerTheorem(EMPTY_PROOF_CONTEXT, thm)).toThrow(ProofError)
    expect(() => registerTheorem(EMPTY_PROOF_CONTEXT, thm)).toThrow(/rebinds boundary wire/)
  })

  it('rejects a forward ends-spawn on the boundary wire', () => {
    const { lhs, rhs, lw, lpin } = topToR()
    const thm: Theorem = {
      name: 'topImpliesR_fwd', lhs, rhs,
      actions: [
        singleStepAction('spawn R end', {
          rule: 'endsSpawn', wire: lw, sites: [{ region: lhs.diagram.root, args: [] }],
        }),
        singleStepAction('shed pin', {
          rule: 'vacuity', direction: 'delete',
          instance: { kind: 'pin', wire: lw, node: lpin, region: lhs.diagram.root },
        }),
      ],
    }
    expect(() => registerTheorem(EMPTY_PROOF_CONTEXT, thm)).toThrow(/rebinds boundary wire/)
  })

  it('still accepts severing a boundary wire (the new wire is a genuine local)', () => {
    // lhs: P() ∧ Q() on one boundary wire R; rhs: R applied as P, fresh Q' applied.
    const left = new DiagramBuilder()
    const p = left.atom(left.root, PROP)
    const q = left.atom(left.root, PROP)
    const R = left.wire([{ node: p, port: { kind: 'head' } }, { node: q, port: { kind: 'head' } }], PROP)
    const lhs = left.buildOpen([R])
    const right = new DiagramBuilder()
    const rp = right.atom(right.root, PROP)
    const rq = right.atom(right.root, PROP)
    const rR = right.wire([{ node: rp, port: { kind: 'head' } }], PROP)
    const rQ = right.wire([{ node: rq, port: { kind: 'head' } }], PROP)
    right.pin(rR, right.root)
    right.pin(rQ, right.root)
    const rhs = right.buildOpen([rR])
    const thm: Theorem = {
      name: 'severBoundary', lhs, rhs,
      actions: [singleStepAction('sever', {
        rule: 'wireSever',
        input: { wire: R, keep: [{ node: p, port: { kind: 'head' } }] },
      })],
    }
    expect(() => registerTheorem(EMPTY_PROOF_CONTEXT, thm)).not.toThrow()
  })
})
```

If the third test's rhs does not match the forward replay's result exactly (pin placement), adjust the rhs pins to mirror `applyWireSever`'s completion (`completeWireEnds` adds pins at the old scope until two ends: `rR` gets one pin because it has one head + the frame entry counts only in `buildOpen`, not in the closed replay — so after replay `rR` has head + frame pin + completion pin; build the rhs so the pinned replay of rhs is iso to that). Use `THEOREM_DEBUG=1` to print both sides if it fails; the test's purpose is only that the boundary guard does not fire, so `toThrow(/rebinds boundary wire/)` negated is an acceptable fallback assertion: `expect(() => registerTheorem(...)).not.toThrow(/rebinds boundary wire/)`.

- [ ] **Step 2: Run test to verify it fails**

Run: `npx vitest run --config vitest.config.ts tests/kernel/proof/theorem.test.ts -t "boundary wires"`
Expected: first two FAIL (`expected function to throw`); third passes.

- [ ] **Step 3: Add `reboundWires` to `step.ts`**

After the `ProofStep` type (line ~107) add:

```ts
/**
 * The wires a step REBINDS: the relation wire whose applications it rewrites
 * (the selected local binder of the Lean wire primitives, leaf rules and
 * ends). Such a wire must be a local binder of the region the step acts in;
 * a boundary wire of an open diagram never is, so a theorem replay may not
 * let these steps act on one. Steps that only add incidences to a wire, or
 * split/merge wires (sever, join, identification), are not listed.
 */
export function reboundWires(step: ProofStep): readonly WireId[] {
  switch (step.rule) {
    case 'cutWrap':
    case 'cutAbsorb':
    case 'parallelSplit':
    case 'endsDelete':
    case 'endsSpawn':
    case 'arityShift':
    case 'arityUnshift':
    case 'argPermute':
    case 'argDuplicate':
    case 'argContract':
    case 'argDrop':
    case 'argExtend':
    case 'applyFormal':
    case 'identityLeaf':
    case 'refLeaf':
      return [step.wire]
    case 'parallelFuse':
      return [step.a, step.b]
    case 'refSpawn':
    case 'atomSpawn':
    case 'identityInsert':
    case 'wireJoin':
    case 'erasure':
    case 'wireSever':
    case 'iteration':
    case 'deiteration':
    case 'doubleCutIntro':
    case 'doubleCutElim':
    case 'theorem':
    case 'vacuity':
    case 'presentation':
    case 'identification':
    case 'unfold':
    case 'fold':
    case 'abstractFormal':
    case 'identityAbstract':
    case 'refAbstract':
      return []
  }
}
```

(Exhaustive switch with no default so a new `ProofStep` variant is a compile error here.)

- [ ] **Step 4: Enforce it in `checkTheorem`**

In `src/kernel/proof/theorem.ts`, change `carry` (lines ~88-104) to take the actions and check before transporting:

```ts
  const carry = (initial: readonly WireId[], actions: readonly ProofAction[]) => {
    let boundary = initial
    return {
      afterStep(_d: Diagram, actionIndex: number, stepIndex: number, receipt: StepReceipt): void {
        const step = actions[actionIndex]!.steps[stepIndex]!
        const rebound = reboundWires(step).find((wire) => boundary.includes(wire))
        if (rebound !== undefined) {
          throw new ProofError(
            `theorem '${thm.name}': step ${stepIndex} (${step.rule}) of action ${actionIndex} `
            + `rebinds boundary wire '${rebound}'; a boundary wire is not a local binder`,
          )
        }
        const mapped = transportBoundary(receipt.interface, boundary)
        if (mapped === undefined) {
          const missing = boundary.find((wire) => receipt.interface.image(wire) === undefined)
          throw new ProofError(
            `theorem '${thm.name}': boundary wire '${missing ?? '<unknown>'}' has no semantic image (action ${actionIndex}, step ${stepIndex})`,
          )
        }
        boundary = mapped
      },
      boundary: () => boundary,
    }
  }
  const fwdInterface = carry(thm.lhs.boundary, thm.actions)
  ...
  const bwdInterface = carry(thm.rhs.boundary, backActions)
```

Import `reboundWires` from `'./step'` and `ProofAction` type from `'./action'` if not already imported.

- [ ] **Step 5: Run the test, expect PASS**

Run: `npx vitest run --config vitest.config.ts tests/kernel/proof/theorem.test.ts`
Expected: all PASS.

- [ ] **Step 6: Full suite + tsc**

Run: `npx vitest run --config vitest.config.ts && npx tsc --noEmit -p tsconfig.json`
Expected: green. If a stored theory (`src/theories/*.ts`, `examples/*.json`) fails registration with "rebinds boundary wire", that theorem's proof acted on a boundary wire and is suspect: report the theorem name and the step; do not relax the guard.

- [ ] **Step 7: Commit**

```bash
git add src/kernel/proof/step.ts src/kernel/proof/theorem.ts tests/kernel/proof/theorem.test.ts
git commit -m "fix(proof): theorem replay refuses steps that rebind a boundary wire

pinnedForReplay makes a boundary wire look like a root existential, so
endsSpawn/endsDelete on it certified ⊤ ⊢ R() with R free, from which
applyTheorem derives ⊥. A boundary wire is never a local binder: every
step that rewrites a wire's applications is refused on a boundary wire."
```

---

### Task 5: `invertStep` for `wireJoin` must pick the wire that actually died

**Files:**
- Modify: `src/kernel/proof/compile-content.ts:1117` (export `invertStep`), `:1251-1270` (`wireJoin` case)
- Test: `tests/kernel/proof/compile-content.test.ts`

Why: the inverse assumes `input.b` is the inner (dying) wire. `applyWireJoin` keeps whichever wire has the outer scope; if that is `b`, the inverse severs the wrong endpoint set at the wrong scope and `completeWireEnds` adds a stray pin, so the inverse is not iso to the pre-join diagram. `compileRelationSever` would then fail loudly with "lost the isomorphism".

- [ ] **Step 1: Write the failing test**

Append to `tests/kernel/proof/compile-content.test.ts` (imports: `DiagramBuilder`, `IOTA`, `relSig`, `applyWireJoin` from `'../../../src/kernel/rules/wire-quantifier'`, `applyWireSever`, `invertStep` from `'../../../src/kernel/proof/compile-content'`, `sameDiagram` from `'../../../src/kernel/diagram/canonical/iso'`):

```ts
describe('invertStep for wireJoin', () => {
  /** a: P(a) inside a cut, pinned there. b: Q(b) on the sheet, pinned there. Join a into b (b is outer). */
  function joinFixture() {
    const P = relSig([IOTA])
    const bld = new DiagramBuilder()
    const cut = bld.cut(bld.root)
    const pa = bld.atom(cut, P)
    const qb = bld.atom(bld.root, P)
    const hp = bld.wire([{ node: pa, port: { kind: 'head' } }], P); bld.pin(hp, cut)
    const hq = bld.wire([{ node: qb, port: { kind: 'head' } }], P); bld.pin(hq, bld.root)
    const a = bld.wire([{ node: pa, port: { kind: 'arg', index: 0 } }]); bld.pin(a, cut)
    const b = bld.wire([{ node: qb, port: { kind: 'arg', index: 0 } }]); bld.pin(b, bld.root)
    return { pre: bld.build(), a, b }
  }

  it('severs the wire that died, at its scope, when b was the outer survivor', () => {
    const { pre, a, b } = joinFixture()
    const step = { rule: 'wireJoin', input: { a, b } } as const
    const post = applyWireJoin(pre, step.input)          // inner a (cut) dies into b (sheet)
    expect(post.wires[a]).toBeUndefined()
    const inverse = invertStep(step, pre, post)
    expect(inverse.rule).toBe('wireSever')
    if (inverse.rule !== 'wireSever') throw new Error('unreachable')
    // BUG: dying was taken to be b, so keep = a's old endpoints and scope = sheet.
    const restored = applyWireSever(post, inverse.input, 'backward')
    expect(sameDiagram(restored, pre, [], [])).toBe(true)
  })
})
```

(`sameDiagram(left, right, leftBoundary, rightBoundary)` — check its signature in `src/kernel/diagram/canonical/iso.ts` and adjust the call. `applyWireSever(..., 'backward')` because the cut is negative and the fresh scope is the cut.)

- [ ] **Step 2: Run test to verify it fails**

Run: `npx vitest run --config vitest.config.ts tests/kernel/proof/compile-content.test.ts -t "invertStep for wireJoin"`
Expected: FAIL — either `invertStep` is not exported (compile error) or `sameDiagram` is false. If it is only the export, export it and re-run; the assertion must fail before Step 3.

- [ ] **Step 3: Fix the inverse**

Change `function invertStep(` to `export function invertStep(` and replace the `wireJoin` case body with:

```ts
    case 'wireJoin': {
      const aSurvived = post.wires[step.input.a] !== undefined
      const survivorPost = aSurvived ? step.input.a : step.input.b
      const dyingId = aSurvived ? step.input.b : step.input.a
      const dying = preWire(dyingId)
      const key = (endpoint: Endpoint): string =>
        `${endpoint.node}|${endpoint.port.kind}|${
          endpoint.port.kind === 'head' ? '' : endpoint.port.index}`
      const movedKeys = new Set(dying.endpoints.map(key))
      const keep = post.wires[survivorPost]!.endpoints.filter((endpoint) =>
        !movedKeys.has(key(endpoint)))
      return {
        rule: 'wireSever',
        input: {
          wire: survivorPost,
          keep,
          scope: derivedScope(pre, dyingId),
        },
      }
    }
```

- [ ] **Step 4: Run the test, expect PASS**

Run: `npx vitest run --config vitest.config.ts tests/kernel/proof/compile-content.test.ts`
Expected: all PASS.

- [ ] **Step 5: Full suite + tsc, commit**

```bash
npx vitest run --config vitest.config.ts && npx tsc --noEmit -p tsconfig.json
git add src/kernel/proof/compile-content.ts tests/kernel/proof/compile-content.test.ts
git commit -m "fix(proof): invert wireJoin by the wire that died, not by argument order"
```

---

### Task 6: deiteration subtree search must not swallow errors

**Files:**
- Modify: `src/kernel/rules/iteration.ts:149-166` (`subtreeEvidence`)
- Test: `tests/kernel/rules/iteration.test.ts`

Why: `try { probe = extractSubgraph(...) } catch { continue }` hides every failure of `extractSubgraph` on a candidate cut. The candidate is a validated child cut of a region; `extractSubgraph` on `{ region: parent, regions: [rid], nodes: [], wires: [] }` succeeds for every such cut (the selection is well-formed by construction: the cut is a child of `region.parent`, and every touching wire keeps an inside endpoint plus its boundary entry). A throw there is a kernel invariant violation and must be loud.

- [ ] **Step 1: Remove the try/catch**

Replace lines 157-166 with:

```ts
    const probe = extractSubgraph(diagram, {
      region: region.parent,
      regions: [rid],
      nodes: [],
      wires: [],
    })
```

Also replace line 149 `Object.entries(diagram.regions).sort()` (which sorts `[id, region]` pairs by their string form — `"id,[object Object]"` — and works only by accident) with `Object.entries(diagram.regions).sort(([left], [right]) => left.localeCompare(right))`.

- [ ] **Step 2: Run the iteration and theory suites**

Run: `npx vitest run --config vitest.config.ts tests/kernel/rules/iteration.test.ts tests/kernel/iteration.test.ts tests/theories && npx tsc --noEmit -p tsconfig.json`
Expected: green. If any test now throws from `extractSubgraph` inside `subtreeEvidence`, that is a real defect in candidate construction: read the error message, write a minimal test in `tests/kernel/rules/iteration.test.ts` that reproduces it through `findDeiterationEvidence`, and fix the cause by name (do not reinstate the catch). Report what it was.

- [ ] **Step 3: Commit**

```bash
git add src/kernel/rules/iteration.ts
git commit -m "fix(kernel): deiteration subtree search fails loudly and sorts candidates by id"
```

---

### Task 7: Whole-repo verification

- [ ] **Step 1:** `npx vitest run --config vitest.config.ts` — expect all green.
- [ ] **Step 2:** `npx tsc --noEmit -p tsconfig.json` — expect 0 errors.
- [ ] **Step 3:** `git status --short` — expect only `VisualProof/Audit.lean` (not ours) modified; everything else committed.
- [ ] **Step 4:** Report: list the six commits, and any theory/example proof that had to be reported under Task 2 Step 5 / Task 4 Step 6.
