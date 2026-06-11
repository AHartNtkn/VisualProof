# Plan 10d: Persistence, Backward Completion, Tethers, E2E Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** The final plan: theory persistence in the browser (save/load through the verified JSON road; assembled theorems become citable in-session), the remaining backward actions (un-erase, un-conversion, un-citation), the spec's hover tethers (binder ↔ variable visual linking), the named 10c debt (insert/convert descriptor paths exercised headlessly), and end-to-end browser tests with Playwright.

**Architecture:** Persistence is `src/app/persist.ts` — pure functions from session/context state to a `Theory` value and back, reusing `theoryToJson`/`loadTheory` (no new format); the shell adds download/upload glue. Backward actions extend `session.ts`'s `BackwardAction` union using the same compute-G′-and-forward-step-together pattern with the reproduction assertion; un-citation needs occurrence rewriting WITHOUT the forward polarity gate, which is goal surgery, not a rule — it reuses the kernel's extract/pinned-fingerprint/remove/splice machinery directly, and soundness is preserved because the recorded forward step replays through the REAL gate at checkTheorem time. Tethers are a pure display extension: `renderScene` gains an options argument carrying a hovered node id and emits tether segments from each variable radial's top to its binder arc. E2E runs Playwright against `vite preview` of the built app; if the environment cannot download browser binaries, that task reports the exact blocker rather than faking coverage.

**Tech Stack:** TypeScript strict, Vitest, vite, Playwright (devDependency).

---

## Design decisions (read before implementing)

**Citable session results.** `assembleTheorem` already returns a `Theorem`; `adoptTheorem(s, thm)` (new, session.ts) verifies it via `checkTheorem` against the session ctx and returns a session whose ctx includes it — newly enumerable for citation. The shell's "assemble" flow becomes assemble → check → adopt → status.

**Persistence round-trip.** `sessionTheory(ctx, extras)` (persist.ts) builds a `Theory` from the live context: definitions and relations pass through; theorems = the ctx's map in insertion order (insertion order IS dependency order — adopt appends). `downloadTheory`/`uploadTheory` in the shell serialize via `theoryToJson` to a Blob and parse uploads through `loadTheory` (which re-verifies — the only road in). Uploading REPLACES the context after verification; a failed verification leaves the session untouched and surfaces the error verbatim.

**Backward un-erase.** At goal G, the user supplies a pattern + attachments + region (same inputs as forward insertion) targeting a POSITIVE region of G; G′ = splice (more content); forward step = erasure of exactly the spliced content (G′ → G). Soundness: erasure at positive is the forward rule; the reproduction assertion plus checkTheorem replay carry the proof. The spliced ids are discovered by diffing G′ against G (fresh ids), forming the erasure selection.

**Backward un-conversion.** Conversion is an equivalence: the backward action takes the node and the OLD term (what the node should have said before); G′ = conversion applied backward via `applyConversion(g, node, oldTerm, fuel)` interactively at action time, and the forward step records the certificate for the G′→G direction (swap the certificate sides: the certificate produced for g→g′ is `{leftSteps, rightSteps}`; the forward step converts g′'s term to g's term, justified by `{leftSteps: rightSteps, rightSteps: leftSteps}`).

**Backward un-citation.** The user picks an occurrence of a theorem's RHS in the goal at a POSITIVE region and the session replaces it by the LHS — goal surgery justified by the recorded forward citation (lhs ⟹ rhs at positive gives G′ ⟹ G). The occurrence is verified exactly as `applyTheorem` does (extract, reorder by args, pinned-fingerprint against thm.rhs) but WITHOUT the forward polarity gate, then remove+splice. The forward step `{rule:'theorem', direction:'forward'}` is built against G′ by locating the spliced lhs-occurrence (the splice's fresh content + the same args). The reproduction assertion then guards the whole construction.

**Tethers.** `renderScene(scene, opts?: { hoverNode?: NodeId })`: for the hovered node, every `var`-kind radial (which carries `hueRow` — its binder bar's row) gains a tether: a segment from the radial's TOP point to the midpoint of the binder's arc (same `hueRow`, kind `lam`), drawn in the binder hue at width 2.5. Pure addition; no scene change; the shell passes its hover hit.

**Descriptor→step coverage (10c debt).** Two headless tests drive `insert` and `convert` descriptors through the exact step construction the shell performs, closing the untested glue paths. The iterate-target and joinPorts items stay shell-level (E2E exercises them).

**E2E.** Playwright with the chromium project only; `webServer: vite preview --port 4173` over a fresh `vite build app`. Smoke specs: the app boots (canvas + chrome render, status shows the loaded theories); term entry adds a node (canvas pixel sampling is flaky — assert via the status line and an exposed `window.__vpaDebug` hook the shell sets with diagram node counts; a DELIBERATE, documented test seam, set only when `?debug` is in the URL); a full prove flow (set goal from edit snapshots, backward unwrap, meet, assemble reports success). If `npx playwright install chromium` cannot download in this environment, commit the config + specs, mark the npm script, and report the environmental blocker with the exact command output — do NOT fake a pass or skip silently; the suite must not contain auto-skipping tests, so the playwright specs live OUTSIDE vitest's glob (e2e/ directory, run by `npm run e2e` only).

**File map:**
- Create: `src/app/persist.ts`, `e2e/app.spec.ts`, `playwright.config.ts`
- Modify: `src/app/session.ts` (adopt + three backward actions), `src/app/shell.ts` (persistence buttons, hover pass-through, debug hook, backward menu growth), `src/view/display.ts` (tethers), `src/app/index.ts`, `package.json`
- Tests: `tests/app/persist.test.ts`, extend `tests/app/session.test.ts`, `tests/app/actions.test.ts` (descriptor paths), `tests/view/display.test.ts` (tethers)

---

### Task 1: Adopt + persistence core

**Files:**
- Modify: `src/app/session.ts` (adoptTheorem)
- Create: `src/app/persist.ts`
- Test: `tests/app/persist.test.ts`

- [x] **Step 1: Write the failing tests**

`tests/app/persist.test.ts`:

```ts
import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../src/kernel/term/parse'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { mkDiagramWithBoundary } from '../../src/kernel/diagram/boundary'
import { mkSelection } from '../../src/kernel/diagram/subgraph/selection'
import { loadTheory, theoryToJson } from '../../src/kernel/proof/store'
import { bootBundledContext } from '../../src/app/boot'
import { startSession, applyForward, meet, assembleTheorem, adoptTheorem } from '../../src/app/session'
import { sessionTheory } from '../../src/app/persist'

const noConsts = new Set<string>()
const p = (s: string) => parseTerm(s, noConsts)

function provenToy(boot = bootBundledContext()) {
  const l = new DiagramBuilder()
  l.termNode(l.root, p('\\x. x'))
  const lhs = mkDiagramWithBoundary(l.build(), [])
  const r = new DiagramBuilder()
  const m = r.termNode(r.root, p('\\x. x'))
  const c1 = r.cut(r.root)
  r.cut(c1)
  void m
  const rhs = mkDiagramWithBoundary(r.build(), [])
  let s = startSession(lhs, rhs, boot.ctx)
  s = applyForward(s, {
    rule: 'doubleCutIntro',
    sel: mkSelection(s.forward.current, { region: s.forward.current.root, regions: [], nodes: [], wires: [] }),
  })
  expect(meet(s)).toBe(true)
  return { s, boot }
}

describe('adoptTheorem', () => {
  it('a checked session result becomes citable in the session context', () => {
    const { s } = provenToy()
    const thm = assembleTheorem(s, 'toy')
    const s2 = adoptTheorem(s, thm)
    expect(s2.ctx.theorems.has('toy')).toBe(true)
    expect(s.ctx.theorems.has('toy')).toBe(false) // immutably extended
  })

  it('refuses duplicate names and unverifiable theorems loudly', () => {
    const { s } = provenToy()
    const thm = assembleTheorem(s, 'toy')
    const s2 = adoptTheorem(s, thm)
    expect(() => adoptTheorem(s2, thm)).toThrowError(/already names a theorem/)
    const forged = { ...thm, steps: [] }
    expect(() => adoptTheorem(s, forged)).toThrowError(/does not arrive/)
  })
})

describe('sessionTheory + the file road', () => {
  it('round-trips the live context (with an adopted theorem) through theory JSON', () => {
    const { s, boot } = provenToy()
    const s2 = adoptTheorem(s, assembleTheorem(s, 'toy'))
    const theory = sessionTheory(s2.ctx, { relations: boot.relations })
    const { ctx } = loadTheory(JSON.parse(JSON.stringify(theoryToJson(theory))))
    expect(ctx.theorems.has('toy')).toBe(true)
    expect(ctx.theorems.has('zeroIsNat')).toBe(true)
  })

  it('preserves dependency order: adopted theorems come after what they cite', () => {
    const { s, boot } = provenToy()
    const s2 = adoptTheorem(s, assembleTheorem(s, 'toy'))
    const theory = sessionTheory(s2.ctx, { relations: boot.relations })
    const names = theory.theorems.map((t) => t.name)
    expect(names.indexOf('toy')).toBeGreaterThan(names.indexOf('zeroIsNat'))
  })
})
```

- [x] **Step 2: Run tests to verify they fail**

- [x] **Step 3: Implement**

In `src/app/session.ts`, add (import `checkTheorem` from the proof barrel path used elsewhere in src/app):

```ts
/** Verify and add a finished theorem to the session context — citable from now on. */
export function adoptTheorem(s: ProofSession, thm: Theorem): ProofSession {
  if (s.ctx.theorems.has(thm.name)) {
    throw new Error(`'${thm.name}' already names a theorem in this session`)
  }
  checkTheorem(thm, s.ctx)
  const theorems = new Map(s.ctx.theorems)
  theorems.set(thm.name, thm)
  return { ...s, ctx: { definitions: s.ctx.definitions, theorems } }
}
```

`src/app/persist.ts`:

```ts
import type { DiagramWithBoundary } from '../kernel/diagram/boundary'
import type { ProofContext } from '../kernel/proof/step'
import type { Theory } from '../kernel/proof/store'

/**
 * The live context as a saveable Theory. Map insertion order IS dependency
 * order (boot loads verified theories in order; adopt appends), which is
 * exactly what verifyTheory requires of the theorems array.
 */
export function sessionTheory(
  ctx: ProofContext,
  extras: { readonly relations: Readonly<Record<string, DiagramWithBoundary>> },
): Theory {
  return {
    definitions: ctx.definitions,
    relations: extras.relations,
    theorems: [...ctx.theorems.values()],
  }
}
```

- [x] **Step 4: Verify PASS, full suite, typecheck**

- [x] **Step 5: Commit**

```bash
git add src/app/session.ts src/app/persist.ts tests/app/persist.test.ts
git commit -m "feat(app): adopt session theorems; live context as a saveable theory"
```

---

### Task 2: The remaining backward actions

**Files:**
- Modify: `src/app/session.ts`
- Test: extend `tests/app/session.test.ts`

- [x] **Step 1: Write the failing tests** — append to `tests/app/session.test.ts`:

```ts
describe('backward un-erase, un-conversion, un-citation', () => {
  it('un-erase adds content backward and records the forward erasure', () => {
    const ctx = verifyTheory(buildFregeTheory())
    // goal: a single node; backward: the proof "had" an extra node erased
    const l = new DiagramBuilder()
    l.termNode(l.root, p('\\x. x'))
    const both = new DiagramBuilder()
    both.termNode(both.root, p('\\x. x'))
    both.termNode(both.root, p('\\x. \\y. x'))
    const lhs = mkDiagramWithBoundary(both.build(), [])
    const rhs = mkDiagramWithBoundary(l.build(), [])
    let s = startSession(lhs, rhs, ctx)
    const pat = new DiagramBuilder()
    pat.termNode(pat.root, p('\\x. \\y. x'))
    s = applyBackward(s, {
      kind: 'unErase',
      region: s.backward.current.root,
      pattern: mkDiagramWithBoundary(pat.build(), []),
      attachments: [],
    })
    expect(s.backward.steps[0]!.rule).toBe('erasure')
    expect(meet(s)).toBe(true)
    const thm = assembleTheorem(s, 'unErased')
    expect(() => checkTheorem(thm, ctx)).not.toThrow()
  })

  it('un-conversion rewrites a node term backward with a swapped certificate', () => {
    const ctx = verifyTheory(buildFregeTheory())
    const l = new DiagramBuilder()
    l.termNode(l.root, p('(\\a. a) y'))
    const lhs = mkDiagramWithBoundary(l.build(), [])
    const r = new DiagramBuilder()
    const m = r.termNode(r.root, p('y'))
    const rhs = mkDiagramWithBoundary(r.build(), [])
    let s = startSession(lhs, rhs, ctx)
    s = applyBackward(s, { kind: 'unConvert', node: m, term: p('(\\a. a) y'), fuel: 32 })
    expect(s.backward.steps[0]!.rule).toBe('conversion')
    expect(meet(s)).toBe(true)
    const thm = assembleTheorem(s, 'unConverted')
    expect(() => checkTheorem(thm, ctx)).not.toThrow()
  })

  it('un-citation replaces a theorem rhs-occurrence by its lhs in the goal', () => {
    const consts2 = new Set(['ZERO'])
    const ctx = verifyTheory(buildFregeTheory())
    // lhs: bare ZERO node. rhs (goal): zeroIsNat's conclusion shape — built by
    // citing forward once, then used as the goal of a FRESH session
    const h = new DiagramBuilder()
    const nz = h.termNode(h.root, parseTerm('ZERO', consts2))
    const wz = h.wire(h.root, [{ node: nz, port: { kind: 'output' } }])
    const lhs = mkDiagramWithBoundary(h.build(), [wz])
    let warm = startSession(lhs, lhs, ctx)
    warm = applyForward(warm, {
      rule: 'theorem', name: 'zeroIsNat', direction: 'forward',
      at: { sel: mkSelection(warm.forward.current, { region: warm.forward.current.root, regions: [], nodes: [nz], wires: [] }), args: [wz] },
    })
    const rhs = mkDiagramWithBoundary(warm.forward.current, [wz])
    let s = startSession(lhs, rhs, ctx)
    // pick the rhs occurrence in the GOAL: the ℕ cut + the evidence node + base line
    const g = s.backward.current
    const cut = Object.entries(g.regions).find(([, r]) => r.kind === 'cut' && r.parent === g.root)![0]
    const evidence = Object.entries(g.nodes).filter(([, n]) => n.kind === 'term' && n.region === g.root).map(([id]) => id)
    const baseLine = Object.entries(g.wires).find(([id, w]) =>
      id !== wz && w.scope === g.root && w.endpoints.every((ep) => g.nodes[ep.node]!.region !== g.root))?.[0]
    s = applyBackward(s, {
      kind: 'unCite',
      name: 'zeroIsNat',
      at: {
        sel: {
          region: g.root,
          regions: [cut],
          nodes: evidence,
          wires: baseLine === undefined ? [] : [baseLine],
        },
        args: [wz],
      },
    })
    expect(s.backward.steps[0]!.rule).toBe('theorem')
    expect(meet(s)).toBe(true)
    const thm = assembleTheorem(s, 'unCited')
    expect(() => checkTheorem(thm, ctx)).not.toThrow()
  })
})
```

NOTE: the un-citation test's occurrence selection mirrors `deriveOneIsNat`'s second-citation discovery (the base line listed explicitly when present). zeroIsNat's RHS includes the evidence ZERO node on wz — the selection must contain exactly the rhs-shape items: the cut, the evidence node(s) that belong to the rhs (zeroIsNat's rhs contains the lhs evidence node — check `buildFregeTheory().theorems[0].rhs` and adjust the picked node set to match its node count; iterate per the discovery idiom, reporting adjustments).

- [x] **Step 2: Run to verify the new tests fail** (unknown action kinds)

- [x] **Step 3: Implement** — extend `BackwardAction` and the switch in `src/app/session.ts`:

```ts
export type BackwardAction =
  | { readonly kind: 'unDoubleCut'; readonly outer: RegionId }
  | { readonly kind: 'unVacuousBubble'; readonly bubble: RegionId }
  | { readonly kind: 'unErase'; readonly region: RegionId; readonly pattern: DiagramWithBoundary; readonly attachments: readonly WireId[] }
  | { readonly kind: 'unConvert'; readonly node: NodeId; readonly term: Term; readonly fuel: number }
  | { readonly kind: 'unCite'; readonly name: string; readonly at: TheoremApplication }
```

Cases (new imports: `spliceSubgraph`, `removeSubgraph`, `extractSubgraph`, `boundaryFingerprint`, `mkDiagramWithBoundary`, `polarity`, `applyConversion`, types `Term`, `NodeId`, `WireId`, `DiagramWithBoundary`, `TheoremApplication`):

```ts
    case 'unErase': {
      if (polarity(g, action.region) !== 'positive') {
        throw new Error(`un-erase targets a positive region (the forward erasure's gate); '${action.region}' is negative`)
      }
      gPrime = spliceSubgraph(g, action.region, action.pattern, action.attachments)
      const regions = Object.keys(gPrime.regions).filter((id) => g.regions[id] === undefined && (gPrime.regions[id] as { parent?: RegionId }).parent === action.region)
      const nodes = Object.keys(gPrime.nodes).filter((id) => g.nodes[id] === undefined && gPrime.nodes[id]!.region === action.region)
      const wires = Object.keys(gPrime.wires).filter((id) => g.wires[id] === undefined && gPrime.wires[id]!.scope === action.region)
      step = { rule: 'erasure', sel: { region: action.region, regions, nodes, wires } }
      break
    }
    case 'unConvert': {
      const node = g.nodes[action.node]
      if (node === undefined || node.kind !== 'term') throw new Error(`'${action.node}' is not a term node`)
      const res = applyConversion(g, action.node, action.term, action.fuel)
      gPrime = res.diagram
      step = {
        rule: 'conversion', node: action.node, term: node.term,
        certificate: { leftSteps: res.certificate.rightSteps, rightSteps: res.certificate.leftSteps },
        attachments: {},
      }
      break
    }
    case 'unCite': {
      const thm = s.ctx.theorems.get(action.name)
      if (thm === undefined) throw new Error(`unknown theorem '${action.name}'`)
      if (polarity(g, action.at.sel.region) !== 'positive') {
        throw new Error(`un-citation targets a positive region (the forward citation's gate); '${action.at.sel.region}' is negative`)
      }
      // verify the selection IS an rhs-occurrence (applyTheorem's machinery, sans polarity gate)
      const { pattern, attachments, binderStubs } = extractSubgraph(g, action.at.sel)
      if (binderStubs.length > 0) throw new Error('open occurrences cannot be un-cited')
      if (action.at.args.length !== attachments.length || new Set(action.at.args).size !== action.at.args.length) {
        throw new Error(`the selection has ${attachments.length} attachment wires; arguments must list each exactly once`)
      }
      const reordered = action.at.args.map((a) => {
        const j = attachments.indexOf(a)
        if (j === -1) throw new Error(`argument wire '${a}' is not an attachment of the selection`)
        return pattern.boundary[j]!
      })
      if (boundaryFingerprint(mkDiagramWithBoundary(pattern.diagram, reordered)) !== boundaryFingerprint(thm.rhs)) {
        throw new Error(`the selection is not an occurrence of '${action.name}' right-hand side`)
      }
      const spliced = spliceSubgraph(g, action.at.sel.region, thm.lhs, action.at.args)
      gPrime = removeSubgraph(spliced, action.at.sel)
      // the forward citation references the spliced LHS occurrence in G′
      const lhsRegions = Object.keys(gPrime.regions).filter((id) => g.regions[id] === undefined && (gPrime.regions[id] as { parent?: RegionId }).parent === action.at.sel.region)
      const lhsNodes = Object.keys(gPrime.nodes).filter((id) => g.nodes[id] === undefined && gPrime.nodes[id]!.region === action.at.sel.region)
      const lhsWires = Object.keys(gPrime.wires).filter((id) => g.wires[id] === undefined && gPrime.wires[id]!.scope === action.at.sel.region)
      step = {
        rule: 'theorem', name: action.name, direction: 'forward',
        at: { sel: { region: action.at.sel.region, regions: lhsRegions, nodes: lhsNodes, wires: lhsWires }, args: action.at.args },
      }
      break
    }
```

CAVEAT (binding): the splice-first-then-remove ORDER in unCite mirrors applyTheorem's resurrection-safe order. The fresh-id diffs identify exactly the spliced content because splice mints ids avoiding the WHOLE pre-removal diagram. The wires diff for the forward selection must list only root-of-occurrence-scoped INTERNAL wires (fresh ⇒ spliced ⇒ internal ✓). If the reproduction assertion fires on any of the three new actions during testing, that is a discovery/diff bug in the session — fix the diff, never weaken the assertion.

- [x] **Step 4: Verify PASS, full suite, typecheck**

- [x] **Step 5: Commit**

```bash
git add src/app/session.ts tests/app/session.test.ts
git commit -m "feat(app): backward un-erase, un-conversion, un-citation"
```

---

### Task 3: Tethers + descriptor coverage + shell growth

**Files:**
- Modify: `src/view/display.ts` (hover tethers), `tests/view/display.test.ts`
- Modify: `tests/app/actions.test.ts` (insert/convert descriptor→step paths)
- Modify: `src/app/shell.ts` (hover pass-through; persistence buttons calling Task 1; backward menu entries for Task 2's actions; the `?debug` window hook for E2E)
- Modify: `src/app/index.ts` (export persist + adopt)

- [x] **Step 1: Tether tests** — append to `tests/view/display.test.ts`:

```ts
describe('hover tethers', () => {
  it('emits one tether per var radial of the hovered node, in the binder hue', () => {
    const h = new DiagramBuilder()
    const n = h.termNode(h.root, p('\\x. \\y. x y'))
    const d = h.build()
    const s = settle(d, initialState(d), DEFAULT_PARAMS, 20000)
    const sceneV = buildScene(d, s.positions)
    const plain = renderScene(sceneV)
    const hovered = renderScene(sceneV, { hoverNode: n })
    expect(hovered.length).toBeGreaterThan(plain.length)
    const tethers = hovered.filter((x) => x.kind === 'segment' && x.width === 2.5)
    expect(tethers).toHaveLength(2) // one per variable occurrence: x and y
  })

  it('no hover, no tethers (output unchanged)', () => {
    const h = new DiagramBuilder()
    h.termNode(h.root, p('\\x. x'))
    const d = h.build()
    const s = settle(d, initialState(d), DEFAULT_PARAMS, 20000)
    const sceneV = buildScene(d, s.positions)
    expect(renderScene(sceneV)).toEqual(renderScene(sceneV, {}))
  })
})
```

- [x] **Step 2: Descriptor-path tests** — append to `tests/app/actions.test.ts`:

```ts
describe('descriptor → step construction (the shell contract)', () => {
  it('insert: an enumerated insert commits as the shell builds it', () => {
    const h = new DiagramBuilder()
    const cut = h.cut(h.root)
    const d = h.build()
    const ctx = verifyTheory(buildFregeTheory())
    const sel = mkSelection(d, { region: cut, regions: [], nodes: [], wires: [] })
    expect(applicableActions(d, sel, ctx).map((a) => a.kind)).toContain('insert')
    const b = new DiagramBuilder()
    b.termNode(b.root, p('\\x. \\y. x'))
    const pattern = mkDiagramWithBoundary(b.build(), [])
    const { applyStep } = await import('../../src/kernel/proof/step')
    const out = applyStep(d, { rule: 'insertion', region: cut, pattern, attachments: [], binders: {} }, ctx)
    expect(Object.values(out.nodes)).toHaveLength(1)
  })

  it('convert: an enumerated convert commits via the certificate path', () => {
    const h = new DiagramBuilder()
    const n = h.termNode(h.root, p('(\\a. a) y'))
    const d = h.build()
    const ctx = verifyTheory(buildFregeTheory())
    const sel = mkSelection(d, { region: d.root, regions: [], nodes: [n], wires: [] })
    expect(applicableActions(d, sel, ctx).map((a) => a.kind)).toContain('convert')
    const { applyConversion } = await import('../../src/kernel/rules/conversion')
    const { applyStep } = await import('../../src/kernel/proof/step')
    const target = p('y')
    const pre = applyConversion(d, n, target, 32)
    const out = applyStep(d, { rule: 'conversion', node: n, term: target, certificate: pre.certificate, attachments: {} }, ctx)
    expect(JSON.stringify(out.nodes[n])).toContain('"port"')
  })
})
```

(NOTE: top-level `await import` inside non-async `it` is invalid — make those `it` callbacks `async`, or hoist the imports to the top of the file like every other import; HOIST them, matching house style. The dynamic-import spelling above is plan shorthand only.)

- [x] **Step 3: Implement** — display.ts: `export function renderScene(scene: Scene, opts: { hoverNode?: NodeId } = {}): Shape[]`; after pushing a hovered node's radials, for each `var` radial compute its top point `polar(angle, r0)` and its binder arc (the `lam` arc with the same `hueRow`); tether = segment from the radial top to `polar((arc.a0 + arc.a1) / 2, arc.r)`, stroke `binderHue(hueRow)`, width 2.5. Shell: pass the current hover's node id; add Save (download Blob of `theoryToJson(sessionTheory(...))`) and Load (file input → JSON.parse → loadTheory → replace ctx) buttons; backward menu entries for the three new actions (un-erase reuses the pattern input; un-convert the term input + fuel; un-cite the citation flow at positive); assemble flow adopts on success; when `location.search` contains `debug`, set `window.__vpaDebug = { nodeCount: () => ..., status: () => ... }` (documented as the E2E seam).

- [x] **Step 4: Verify PASS, full suite, typecheck, `npx vite build app`**

- [x] **Step 5: Commit**

```bash
git add src/view/display.ts tests/view/display.test.ts tests/app/actions.test.ts src/app/shell.ts src/app/index.ts
git commit -m "feat(app): hover tethers, persistence chrome, descriptor coverage, debug seam"
```

---

### Task 4: E2E

**Files:**
- Create: `playwright.config.ts`, `e2e/app.spec.ts`
- Modify: `package.json` (`"e2e": "playwright test"`, playwright devDependency)

- [x] **Step 1: Install** — `npm install -D @playwright/test`, then `npx playwright install chromium`. IF THE BINARY DOWNLOAD FAILS in this environment: still commit config+specs+script, and report the exact failing command output as the environmental blocker — no fake passes, no silent skips (the e2e/ directory is outside vitest's glob, so the unit suite stays honest).

- [x] **Step 2: Config** — `playwright.config.ts`:

```ts
import { defineConfig } from '@playwright/test'

export default defineConfig({
  testDir: 'e2e',
  use: { baseURL: 'http://localhost:4173' },
  webServer: {
    command: 'npx vite build app --logLevel error && npx vite preview app --port 4173 --strictPort',
    url: 'http://localhost:4173',
    reuseExistingServer: false,
    timeout: 60000,
  },
  projects: [{ name: 'chromium', use: { browserName: 'chromium' } }],
})
```

- [x] **Step 3: Specs** — `e2e/app.spec.ts`:

```ts
import { test, expect } from '@playwright/test'

declare global {
  interface Window {
    __vpaDebug?: { nodeCount(): number; status(): string }
  }
}

test('the app boots with both theories loaded', async ({ page }) => {
  await page.goto('/?debug')
  await expect(page.locator('canvas')).toBeVisible()
  await expect(page.locator('#chrome')).toContainText('zeroIsNat')
  const status = await page.evaluate(() => window.__vpaDebug!.status())
  expect(status.toLowerCase()).toContain('loaded')
})

test('term entry adds a node to the edit diagram', async ({ page }) => {
  await page.goto('/?debug')
  const before = await page.evaluate(() => window.__vpaDebug!.nodeCount())
  await page.getByPlaceholder(/term/i).fill('\\x. x')
  await page.getByRole('button', { name: /add/i }).click()
  const after = await page.evaluate(() => window.__vpaDebug!.nodeCount())
  expect(after).toBe(before + 1)
})

test('a goal proves end to end through the chrome', async ({ page }) => {
  await page.goto('/?debug')
  // build lhs: one identity node; snapshot as lhs
  await page.getByPlaceholder(/term/i).fill('\\x. x')
  await page.getByRole('button', { name: /add/i }).click()
  await page.getByRole('button', { name: /set lhs/i }).click()
  // wrap it in a double cut via the edit buttons to form the rhs… simplest:
  // set rhs = same diagram, prove with zero steps (met immediately)
  await page.getByRole('button', { name: /set rhs/i }).click()
  await page.getByRole('button', { name: /prove/i }).click()
  await page.getByRole('button', { name: /assemble/i }).click()
  const status = await page.evaluate(() => window.__vpaDebug!.status())
  expect(status).toMatch(/checked|met|proved/i)
})
```

NOTE: the chrome's actual control names/placeholders are whatever Task 3's shell produced — READ shell.ts and adjust selectors to the real labels before running; the spec above is the INTENT. Keep selectors role/label-based.

- [x] **Step 4: Run** — `npm run e2e`. Iterate selectors against real failures. All three must pass (or the environmental blocker is reported per Step 1).

- [x] **Step 5: Commit**

```bash
git add playwright.config.ts e2e/ package.json package-lock.json
git commit -m "test(e2e): app boot, term entry, prove flow"
```

---

### Task 5: Battery + completion

**Files:**
- Test: extend `tests/app/pipeline.test.ts`

- [x] **Step 1: The closing battery** — append:

```ts
describe('the full story: prove, adopt, save, reload, cite', () => {
  it('a session theorem survives the file road and is citable after reload', async () => {
    const { bootBundledContext } = await import('../../src/app/boot')
    const { adoptTheorem } = await import('../../src/app/session')
    const { sessionTheory } = await import('../../src/app/persist')
    const { loadTheory, theoryToJson } = await import('../../src/kernel/proof/store')
    const boot = bootBundledContext()
    // prove the toy double-cut theorem forward
    const l = emptyDiagram()
    const { diagram: lhsD } = addTermNode(l, l.root, p('\\x. x'))
    const lhs = mkDiagramWithBoundary(lhsD, [])
    let s = startSession(lhs, lhs, boot.ctx)
    s = applyForward(s, {
      rule: 'doubleCutIntro',
      sel: mkSelection(s.forward.current, { region: s.forward.current.root, regions: [], nodes: [], wires: [] }),
    })
    const rhs = mkDiagramWithBoundary(s.forward.current, [])
    s = { ...s, rhs, backward: { ...s.backward, current: rhs.diagram } }
    const thm = assembleTheorem(s, 'wrapId')
    const s2 = adoptTheorem(s, thm)
    // save, reload, verify, cite
    const text = JSON.stringify(theoryToJson(sessionTheory(s2.ctx, { relations: boot.relations })))
    const { ctx } = loadTheory(JSON.parse(text))
    expect(ctx.theorems.has('wrapId')).toBe(true)
  })
})
```

(NOTE: hoist the dynamic imports to top-level imports per house style; the session-rhs splice `s = { ...s, rhs, ... }` is test-level state surgery to make a met session without re-running — acceptable in a test, with this comment carried over.)

- [x] **Step 2: Run; full gates** (`vitest`, `tsc`, `vite build app`, and `npm run e2e` if Task 4 unblocked).

- [x] **Step 3: Commit**

```bash
git add tests/app/pipeline.test.ts
git commit -m "test(app): prove-adopt-save-reload-cite closing battery"
```

---

## Completion criteria for this plan

- `npx vitest run` green, `npx tsc --noEmit` clean, `npx vite build app` compiles, `npm run e2e` passes (or its environmental blocker is documented in the execution record with exact output).
- Demonstrated: adopted theorems are immediately citable and survive the save/reload road in dependency order; all five backward action kinds construct reproduction-asserted forward steps and assemble into checked theorems; hover emits exactly one tether per variable occurrence in the binder hue and nothing otherwise; the insert/convert descriptor paths are headlessly exercised; the browser flow boots, edits, and proves.
- This completes the planned sequence (Plans 1–10d).

## Carried obligations (post-MVP)

- General +-commutativity (induction at scale), open theorem sides/abstraction, matcher symmetry/bare-wire, R(x,x) abstraction, joinPorts deepest-common-ancestor, in-session relation NAMING UI, PiP/split visual companion target.
