# Plan 8: Proof Objects, Derived Rules, Theory Store Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Serializable, mechanically replayable proofs; theorems as derived rules applied natively (never expanded); bidirectional (meet-in-the-middle) proof composition; a verified theory store with a JSON file format.

**Architecture:** A new `src/kernel/proof/` layer on top of `rules/`. A `ProofStep` is a serializable record of one rule application; `replayProof` folds steps with each applier enforcing its own gate (the LCF guarantee — replay IS re-verification). A `Theorem` is `lhs ⟹ rhs` between same-arity `DiagramWithBoundary`s, proven by steps transforming `lhs.diagram` into `rhs.diagram` with boundary wires preserved; `applyTheorem` is the derived-rule application: polarity-gated occurrence rewriting verified by boundary-pinned fingerprints (the same exactness machinery as comprehension abstraction), one remove+splice — the stored proof is never inlined. Meet-in-the-middle composition rewrites the backward tail's ids through canonical-labeling isomorphisms, re-derived after every step. The theory store is an ordered list of theorems (later ones may use earlier ones), verified in registration order; loading a theory file re-verifies everything.

**Tech Stack:** TypeScript strict, Vitest, no runtime deps.

---

## Design decisions (read before implementing)

**Replay is verification.** A proof object carries no trust: `replayProof` applies each step through the real appliers, which throw on any gate violation. Conversion steps replay via `applyConversionByCertificate` — fuel-free per spec §3.7 (the certificate was produced once at construction time by `applyConversion`). Deiteration steps record their fuel: the matcher is deterministic, so replay reproduces the original search exactly.

**Theorems generalize sentences.** `Theorem = { name, lhs, rhs, steps }` with `lhs`/`rhs` both `DiagramWithBoundary` of equal arity. A sentence implication is the arity-0 case; `blank ⟹ T` (a theorem in the spec's sense) is the case where `lhs.diagram` is empty. `checkTheorem` replays `steps` from `lhs.diagram` and requires (a) every `lhs.boundary` wire still exists in the result (a proof that destroys a boundary wire — e.g. wire-joins it away as the inner wire — is refused loudly; keep boundary wires as the outer wire of any join), and (b) `boundaryFingerprint(result pinned by lhs.boundary) === boundaryFingerprint(rhs)`. Both sides' boundary wires must be scoped at their diagram roots (splice's stub invariant) — checked up front.

**Derived rules apply natively.** `applyTheorem(d, thm, at, direction)`: `forward` replaces an occurrence of `lhs` by `rhs` at a POSITIVE region (monotonicity: ∀x⃗ lhs(x⃗)⟹rhs(x⃗) licenses the rewrite); `reverse` replaces an occurrence of `rhs` by `lhs` at a NEGATIVE region. The occurrence is given, not searched: `at = { sel, args }` exactly like comprehension abstraction, verified by extracting `sel`, reordering its boundary by `args`, and comparing pinned fingerprints against the theorem side — exact by the Plan 3 theorem. The rewrite is `removeSubgraph(sel)` then `spliceSubgraph(at.sel.region, otherSide, at.args)` — one step, regardless of how long the stored proof is. Interactive FINDING of occurrences is the matcher's job (UI layer); the kernel only checks.

**Meet-in-the-middle composition.** A bidirectional session builds a forward chain `P → … → M_f` and a backward chain recorded as forward steps `M_b → … → G` (each backward UI action picks a rule application whose RESULT is the current goal). To compose, `M_f` and `M_b` must be isomorphic — but the tail steps reference `M_b`-side ids, and fresh ids generated during replay depend on the id environment, so a single up-front rewrite is not enough. `composeProofs` therefore walks the tail step by step: map the step's ids through the current source→target isomorphism, apply the mapped step to the target side and the original step to the source side, then RE-DERIVE the isomorphism between the two results from their canonical labelings. Appliers are isomorphism-equivariant up to fresh-id choice, so the re-derived iso always exists; a divergence check throws loudly anyway. This needs `canonicalLabeling` — the IR pipeline already ends in a discrete coloring; Task 1 exposes its ordinals instead of discarding them, and `isoBetween` matches ordinals between two labelings with equal forms.

**Id mapping scope.** `mapStepIds` maps host-diagram ids only: region/node/wire id fields, selection contents, attachment lists, endpoint node ids, conversion attachment values, theorem application contents. Embedded patterns (`DiagramWithBoundary` values in insertion/comprehension steps) are self-contained namespaces — never mapped. Terms are never mapped (port names are node-internal).

**Theory files re-verify on load.** `Theory = { definitions, relations, theorems[] }` (theorems ordered — later may cite earlier by name). `verifyTheory` checks definitions well-formed, relations valid, then `checkTheorem` for each theorem against the context accumulated so far, returning the full `ProofContext`. `theoryFromJson` does strict structural validation (mirroring `diagram/json.ts`: `assertOnlyKeys`, no extra fields, loud failures); `loadTheory` composes parsing with verification. There is no trust-without-verify path.

**Error vocabulary.** New `ProofError` for proof-layer failures (replay step failed, theorem check failed, meet mismatch, unknown theorem name, duplicate names). `applyTheorem` is a RULE and keeps the rules vocabulary: RuleError for gate refusals (wrong polarity, occurrence mismatch), DiagramError for malformed input. JSON parsing throws plain Error (`malformed … JSON: …`), matching `diagram/json.ts`.

**File map:**
- Modify: `src/kernel/diagram/canonical/canonical.ts` (expose `canonicalLabeling`), `src/kernel/diagram/canonical/fingerprint.ts` (unchanged API), `src/kernel/diagram/index.ts`, `src/kernel/diagram/json.ts` (export `parsePortKey`)
- Create: `src/kernel/diagram/canonical/iso.ts`
- Create: `src/kernel/proof/{error,step,theorem,compose,json,store,index}.ts`
- Tests: `tests/kernel/diagram/labeling.test.ts`, `tests/kernel/proof/{step,theorem,compose,json,store,endtoend}.test.ts`

---

### Task 1: Canonical labeling + isomorphism extraction

**Files:**
- Modify: `src/kernel/diagram/canonical/canonical.ts`
- Create: `src/kernel/diagram/canonical/iso.ts`
- Modify: `src/kernel/diagram/index.ts` (add exports)
- Test: `tests/kernel/diagram/labeling.test.ts`

- [ ] **Step 1: Write the failing tests**

`tests/kernel/diagram/labeling.test.ts`:

```ts
import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../../src/kernel/term/parse'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { canonicalForm, canonicalLabeling } from '../../../src/kernel/diagram/canonical/canonical'
import { isoBetween } from '../../../src/kernel/diagram/canonical/iso'
import { diagramFingerprint } from '../../../src/kernel/diagram/canonical/fingerprint'
import { mkDiagram } from '../../../src/kernel/diagram/diagram'
import type { Diagram, Region, DiagramNode, Wire } from '../../../src/kernel/diagram/diagram'

const noConsts = new Set<string>()
const p = (s: string) => parseTerm(s, noConsts)

function host() {
  const h = new DiagramBuilder()
  const cut = h.cut(h.root)
  const n = h.termNode(h.root, p('y'))
  const m = h.termNode(cut, p('\\x. x'))
  h.wire(h.root, [
    { node: n, port: { kind: 'freeVar', name: 'y' } },
    { node: m, port: { kind: 'output' } },
  ])
  return h.build()
}

/** The same diagram with every id renamed. */
function renamed(d: Diagram): Diagram {
  const r = (id: string) => `X_${id}`
  const regions: Record<string, Region> = {}
  for (const [id, reg] of Object.entries(d.regions)) {
    regions[r(id)] = reg.kind === 'sheet' ? reg
      : reg.kind === 'cut' ? { kind: 'cut', parent: r(reg.parent) }
      : { kind: 'bubble', parent: r(reg.parent), arity: reg.arity }
  }
  const nodes: Record<string, DiagramNode> = {}
  for (const [id, n] of Object.entries(d.nodes)) {
    nodes[r(id)] = n.kind === 'term'
      ? { kind: 'term', region: r(n.region), term: n.term }
      : { kind: 'atom', region: r(n.region), binder: r(n.binder) }
  }
  const wires: Record<string, Wire> = {}
  for (const [id, w] of Object.entries(d.wires)) {
    wires[r(id)] = { scope: r(w.scope), endpoints: w.endpoints.map((ep) => ({ node: r(ep.node), port: ep.port })) }
  }
  return mkDiagram({ root: r(d.root), regions, nodes, wires })
}

describe('canonicalLabeling', () => {
  it('its form field equals canonicalForm and ordinals are total and distinct', () => {
    const d = host()
    const lab = canonicalLabeling(d)
    expect(lab.form).toBe(canonicalForm(d))
    expect(new Set(lab.regionOrd.values()).size).toBe(Object.keys(d.regions).length)
    expect(new Set(lab.nodeOrd.values()).size).toBe(Object.keys(d.nodes).length)
    expect(new Set(lab.wireOrd.values()).size).toBe(Object.keys(d.wires).length)
  })

  it('assigns the same ordinals to corresponding objects across renamings', () => {
    const d = host()
    const e = renamed(d)
    const ld = canonicalLabeling(d)
    const le = canonicalLabeling(e)
    expect(ld.form).toBe(le.form)
    for (const [id, ord] of ld.nodeOrd) {
      expect(le.nodeOrd.get(`X_${id}`)).toBe(ord)
    }
  })
})

describe('isoBetween', () => {
  it('returns the identity-like mapping between a diagram and its renaming', () => {
    const d = host()
    const e = renamed(d)
    const iso = isoBetween(d, e)
    expect(iso).not.toBeNull()
    for (const id of Object.keys(d.nodes)) expect(iso!.nodes.get(id)).toBe(`X_${id}`)
    for (const id of Object.keys(d.regions)) expect(iso!.regions.get(id)).toBe(`X_${id}`)
    for (const id of Object.keys(d.wires)) expect(iso!.wires.get(id)).toBe(`X_${id}`)
  })

  it('transports structure: mapped parents, regions, scopes, endpoints agree', () => {
    const d = host()
    const e = renamed(d)
    const iso = isoBetween(d, e)!
    for (const [id, n] of Object.entries(d.nodes)) {
      const img = e.nodes[iso.nodes.get(id)!]!
      expect(img.region).toBe(iso.regions.get(n.region))
    }
    for (const [id, w] of Object.entries(d.wires)) {
      const img = e.wires[iso.wires.get(id)!]!
      expect(img.scope).toBe(iso.regions.get(w.scope))
      expect(img.endpoints).toHaveLength(w.endpoints.length)
    }
  })

  it('picks a consistent mapping for symmetric diagrams', () => {
    // two indistinguishable nodes: any of the two isos is fine, but the map
    // must BE an iso — distinct images, structure transported
    const h1 = new DiagramBuilder()
    h1.termNode(h1.root, p('\\x. x'))
    h1.termNode(h1.root, p('\\x. x'))
    const d = h1.build()
    const h2 = new DiagramBuilder()
    h2.termNode(h2.root, p('\\x. x'))
    h2.termNode(h2.root, p('\\x. x'))
    const e = h2.build()
    const iso = isoBetween(d, e)!
    const images = new Set(iso.nodes.values())
    expect(images.size).toBe(2)
    expect(diagramFingerprint(d)).toBe(diagramFingerprint(e))
  })

  it('returns null for non-isomorphic diagrams', () => {
    const h2 = new DiagramBuilder()
    h2.termNode(h2.root, p('y'))
    expect(isoBetween(host(), h2.build())).toBeNull()
  })
})
```

- [ ] **Step 2: Run tests to verify they fail**

Run: `npx vitest run tests/kernel/diagram/labeling.test.ts`
Expected: FAIL — `canonicalLabeling` not exported / cannot resolve `canonical/iso`.

- [ ] **Step 3: Implement**

In `src/kernel/diagram/canonical/canonical.ts`:

1. Add after the imports:

```ts
export type CanonicalLabeling = {
  readonly form: string
  readonly regionOrd: ReadonlyMap<RegionId, number>
  readonly nodeOrd: ReadonlyMap<NodeId, number>
  readonly wireOrd: ReadonlyMap<WireId, number>
}
```

2. Replace the body of `canonicalForm` and add `canonicalLabeling`:

```ts
export function canonicalForm(d: Diagram, pinnedWires: readonly WireId[] = []): string {
  return canonicalLabeling(d, pinnedWires).form
}

/**
 * The canonical form together with the winning discrete coloring's ordinals.
 * Corresponding objects of isomorphic diagrams receive equal ordinals — the
 * basis for isomorphism extraction (iso.ts) and proof composition (Plan 8).
 */
export function canonicalLabeling(d: Diagram, pinnedWires: readonly WireId[] = []): CanonicalLabeling {
  const seenPins = new Set<string>()
  for (const w of pinnedWires) {
    if (d.wires[w] === undefined) throw new DiagramError(`pinned wire '${w}' does not exist`)
    if (seenPins.has(w)) throw new DiagramError(`duplicate pinned wire '${w}'`)
    seenPins.add(w)
  }
  const idx = buildIndex(d, pinnedWires)
  const { form, colors } = search(idx, refine(idx, initialColors(idx)))
  return {
    form,
    regionOrd: ordinalize(idx.regionIds, colors.region),
    nodeOrd: ordinalize(idx.nodeIds, colors.node),
    wireOrd: ordinalize(idx.wireIds, colors.wire),
  }
}
```

3. Change `search` to return the winning colors alongside the form:

```ts
function search(idx: Index, c: Colors): { form: string; colors: Colors } {
  const tied = firstTiedClass(c)
  if (tied === null) return { form: serializeWith(idx, c), colors: c }
  let best: { form: string; colors: Colors } | null = null
  for (const member of tied.members) {
    const s = search(idx, refine(idx, individualize(c, tied.sort, member)))
    if (best === null || s.form < best.form) best = s
  }
  return best!
}
```

(`serializeWith`, `ordinalize`, and everything else are unchanged. The original `canonicalForm` body moves into `canonicalLabeling`.)

Create `src/kernel/diagram/canonical/iso.ts`:

```ts
import type { Diagram, NodeId, RegionId, WireId } from '../diagram'
import { DiagramError } from '../diagram'
import { canonicalLabeling } from './canonical'

export type DiagramIso = {
  readonly regions: ReadonlyMap<RegionId, RegionId>
  readonly nodes: ReadonlyMap<NodeId, NodeId>
  readonly wires: ReadonlyMap<WireId, WireId>
}

/**
 * An isomorphism from `from` onto `to`, or null when none exists. Built by
 * matching canonical-labeling ordinals: equal forms mean the discrete
 * colorings correspond, and the ordinal-matched mapping transports all
 * structure (the canonical serialization writes every reference by ordinal).
 * For diagrams with automorphisms this picks one of the valid isomorphisms,
 * deterministically.
 */
export function isoBetween(from: Diagram, to: Diagram): DiagramIso | null {
  const a = canonicalLabeling(from)
  const b = canonicalLabeling(to)
  if (a.form !== b.form) return null
  const invert = (m: ReadonlyMap<string, number>): Map<number, string> => {
    const r = new Map<number, string>()
    for (const [id, o] of m) r.set(o, id)
    return r
  }
  const make = (mA: ReadonlyMap<string, number>, mBInv: Map<number, string>): Map<string, string> => {
    const out = new Map<string, string>()
    for (const [id, o] of mA) {
      const img = mBInv.get(o)
      if (img === undefined) throw new DiagramError(`canonical labelings with equal forms disagree at ordinal ${o}`)
      out.set(id, img)
    }
    return out
  }
  return {
    regions: make(a.regionOrd, invert(b.regionOrd)),
    nodes: make(a.nodeOrd, invert(b.nodeOrd)),
    wires: make(a.wireOrd, invert(b.wireOrd)),
  }
}
```

Append to `src/kernel/diagram/index.ts` (next to the other canonical exports):

```ts
export type { CanonicalLabeling } from './canonical/canonical'
export { canonicalLabeling } from './canonical/canonical'
export type { DiagramIso } from './canonical/iso'
export { isoBetween } from './canonical/iso'
```

- [ ] **Step 4: Verify PASS, full suite, typecheck** (the refactor must not change any existing fingerprint — the full suite is the regression gate)

- [ ] **Step 5: Commit**

```bash
git add src/kernel/diagram/canonical/canonical.ts src/kernel/diagram/canonical/iso.ts src/kernel/diagram/index.ts tests/kernel/diagram/labeling.test.ts
git commit -m "feat(kernel): canonical labeling ordinals and isomorphism extraction"
```

**Review outcome (commit `3ccc0b9`, fix `bffbdff`):** APPROVED; diff-pure refactor (refinement/serialization untouched), zero fingerprint regressions. Discreteness verified: leaf colorings are per-sort injective (cross-sort numeric collisions are harmless since ordinalize is per-sort). Full structural transport verified on automorphic copies. Mutant iii (initial-color ordinals) survived and was killed in `bffbdff`. Mutant iv (lex-max branch choice) is EQUIVALENT: any deterministic selection over the fully-explored tie orbit is isomorphism-invariant, and fingerprints are computed fresh, never persisted — accepted. Note: pin-order swaps on automorphic attachment points correctly fingerprint EQUAL (an order-respecting iso exists via the node swap); pins distinguish structurally distinct attachments only. Suite: 331.

---

### Task 2: Proof steps + theorems (one task — the modules are mutually recursive)

**Files:**
- Create: `src/kernel/proof/error.ts`
- Create: `src/kernel/proof/step.ts`
- Create: `src/kernel/proof/theorem.ts`
- Test: `tests/kernel/proof/step.test.ts`
- Test: `tests/kernel/proof/theorem.test.ts`

**Why one task:** theorem steps ARE proof steps (`applyStep` dispatches to `applyTheorem`) and theorem checking REPLAYS proof steps (`checkTheorem` calls `replayProof`) — the mutual recursion is inherent to derived rules whose proofs may use earlier derived rules. The two modules form a deliberate, benign import cycle: all `import type`s are erased (`verbatimModuleSyntax`), and the two value imports (`applyTheorem` in step.ts, `replayProof` in theorem.ts) are function references only used at call time, which ESM handles. Both modules and both test files land in one commit.

- [ ] **Step 1: Write the failing tests** (both files)

`tests/kernel/proof/step.test.ts`:

```ts
import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../../src/kernel/term/parse'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { mkDiagramWithBoundary } from '../../../src/kernel/diagram/boundary'
import { mkSelection } from '../../../src/kernel/diagram/subgraph/selection'
import { diagramFingerprint } from '../../../src/kernel/diagram/canonical/fingerprint'
import { applyErasure } from '../../../src/kernel/rules/erasure'
import { applyConversion } from '../../../src/kernel/rules/conversion'
import { applyStep, replayProof } from '../../../src/kernel/proof/step'
import type { ProofContext, ProofStep } from '../../../src/kernel/proof/step'
import { ProofError } from '../../../src/kernel/proof/error'

const consts = new Set(['I'])
const p = (s: string) => parseTerm(s, consts)
const noConsts = new Set<string>()
const pp = (s: string) => parseTerm(s, noConsts)

const ctx: ProofContext = { definitions: { I: pp('\\x. x') }, theorems: new Map() }

describe('applyStep mirrors the direct appliers', () => {
  it('erasure step equals applyErasure', () => {
    const h = new DiagramBuilder()
    const n = h.termNode(h.root, pp('\\x. x'))
    h.cut(h.root)
    const d = h.build()
    const sel = mkSelection(d, { region: d.root, regions: [], nodes: [n], wires: [] })
    const step: ProofStep = { rule: 'erasure', sel }
    expect(diagramFingerprint(applyStep(d, step, ctx))).toBe(diagramFingerprint(applyErasure(d, sel)))
  })

  it('conversion step replays by certificate, fuel-free', () => {
    const h = new DiagramBuilder()
    const n = h.termNode(h.root, pp('(\\x. x) y'))
    const d = h.build()
    const { diagram, certificate } = applyConversion(d, n, pp('y'), 10)
    const step: ProofStep = { rule: 'conversion', node: n, term: pp('y'), certificate, attachments: {} }
    expect(diagramFingerprint(applyStep(d, step, ctx))).toBe(diagramFingerprint(diagram))
  })

  it('unfold and fold steps use the context definitions', () => {
    const h = new DiagramBuilder()
    const n = h.termNode(h.root, p('I y'))
    const d = h.build()
    const unfolded = applyStep(d, { rule: 'unfold', node: n, path: ['fn'] }, ctx)
    const refolded = applyStep(unfolded, { rule: 'fold', node: n, path: ['fn'], constId: 'I' }, ctx)
    expect(diagramFingerprint(refolded)).toBe(diagramFingerprint(d))
  })

  it('double-cut intro/elim and iteration/deiteration round-trip through steps', () => {
    const h = new DiagramBuilder()
    const n = h.termNode(h.root, pp('y'))
    const hub = h.termNode(h.root, pp('\\x. x'))
    h.wire(h.root, [
      { node: n, port: { kind: 'freeVar', name: 'y' } },
      { node: hub, port: { kind: 'output' } },
    ])
    const cut = h.cut(h.root)
    const d = h.build()
    const sel = mkSelection(d, { region: d.root, regions: [], nodes: [n], wires: [] })
    const steps: ProofStep[] = [
      { rule: 'iteration', sel, target: cut },
      { rule: 'doubleCutIntro', sel },
    ]
    const out = replayProof(d, steps, ctx)
    expect(Object.keys(out.regions).length).toBe(Object.keys(d.regions).length + 2)
  })

  it('insertion and comprehension steps carry their patterns by value', () => {
    const b = new DiagramBuilder()
    b.termNode(b.root, pp('\\x. \\y. x'))
    const pat = mkDiagramWithBoundary(b.build(), [])
    const h = new DiagramBuilder()
    const cut = h.cut(h.root)
    const d = h.build()
    const out = applyStep(d, { rule: 'insertion', region: cut, pattern: pat, attachments: [] }, ctx)
    expect(Object.values(out.nodes)).toHaveLength(1)
  })
})

describe('replayProof failure reporting', () => {
  it('names the failing step index and rule', () => {
    const h = new DiagramBuilder()
    const cut = h.cut(h.root)
    const n = h.termNode(cut, pp('\\x. x'))
    const d = h.build()
    const sel = mkSelection(d, { region: cut, regions: [], nodes: [n], wires: [] })
    let caught: unknown
    try {
      replayProof(d, [{ rule: 'erasure', sel }], ctx) // negative region: gate refuses
    } catch (e) { caught = e }
    expect(caught).toBeInstanceOf(ProofError)
    expect((caught as Error).message).toMatch(/step 0 \(erasure\) failed: erasure requires a positive region/)
  })

  it('unknown theorem names fail loudly', () => {
    const d = new DiagramBuilder().build()
    expect(() => applyStep(d, {
      rule: 'theorem', name: 'ghost',
      at: { sel: { region: d.root, regions: [], nodes: [], wires: [] }, args: [] },
      direction: 'forward',
    }, ctx)).toThrowError(/unknown theorem 'ghost'/)
  })
})
```

(The second test file, `tests/kernel/proof/theorem.test.ts`, appears below after the implementation sources — write BOTH in this step.)

- [ ] **Step 2: Run tests to verify they fail**

Run: `npx vitest run tests/kernel/proof/step.test.ts tests/kernel/proof/theorem.test.ts`
Expected: FAIL — cannot resolve `proof/step` / `proof/theorem`.

- [ ] **Step 3: Implement**

`src/kernel/proof/error.ts`:

```ts
/** Proof-layer failures: replay errors, theorem-check failures, meet mismatches. */
export class ProofError extends Error {
  constructor(message: string) {
    super(message)
    this.name = 'ProofError'
  }
}
```

`src/kernel/proof/step.ts`:

```ts
import type { Term } from '../term/term'
import type { PathSeg } from '../term/reduce'
import type { ConversionCertificate } from '../term/certificate'
import type { Diagram, Endpoint, NodeId, RegionId, WireId } from '../diagram/diagram'
import type { DiagramWithBoundary } from '../diagram/boundary'
import type { SubgraphSelection } from '../diagram/subgraph/selection'
import { applyInsertion, applyWireJoin } from '../rules/insertion'
import { applyErasure, applyWireSever } from '../rules/erasure'
import { applyIteration, applyDeiteration } from '../rules/iteration'
import { applyDoubleCutIntro, applyDoubleCutElim } from '../rules/doublecut'
import { applyConversionByCertificate } from '../rules/conversion'
import { applyFusion, applyFission } from '../rules/fusion'
import { applyUnfold, applyFold } from '../rules/definitions'
import type { Definitions } from '../rules/definitions'
import { applyComprehensionInstantiate, applyComprehensionAbstract } from '../rules/comprehension'
import type { AbstractionOccurrence } from '../rules/comprehension'
import type { Theorem, TheoremApplication } from './theorem'
import { applyTheorem } from './theorem'
import { ProofError } from './error'

export type ProofContext = {
  readonly definitions: Definitions
  readonly theorems: ReadonlyMap<string, Theorem>
}

/**
 * One serializable rule application. Replay carries no trust: applyStep calls
 * the real appliers, each enforcing its own gate. Conversion replays by
 * certificate (fuel-free, §3.7); deiteration records its fuel (the matcher is
 * deterministic, so replay reproduces the original search).
 */
export type ProofStep =
  | { readonly rule: 'insertion'; readonly region: RegionId; readonly pattern: DiagramWithBoundary; readonly attachments: readonly WireId[] }
  | { readonly rule: 'wireJoin'; readonly a: WireId; readonly b: WireId }
  | { readonly rule: 'erasure'; readonly sel: SubgraphSelection }
  | { readonly rule: 'wireSever'; readonly wire: WireId; readonly keep: readonly Endpoint[] }
  | { readonly rule: 'iteration'; readonly sel: SubgraphSelection; readonly target: RegionId }
  | { readonly rule: 'deiteration'; readonly sel: SubgraphSelection; readonly fuel: number }
  | { readonly rule: 'doubleCutIntro'; readonly sel: SubgraphSelection }
  | { readonly rule: 'doubleCutElim'; readonly region: RegionId }
  | { readonly rule: 'conversion'; readonly node: NodeId; readonly term: Term; readonly certificate: ConversionCertificate; readonly attachments: Readonly<Record<string, WireId>> }
  | { readonly rule: 'fusion'; readonly wire: WireId }
  | { readonly rule: 'fission'; readonly node: NodeId; readonly path: readonly PathSeg[] }
  | { readonly rule: 'unfold'; readonly node: NodeId; readonly path: readonly PathSeg[] }
  | { readonly rule: 'fold'; readonly node: NodeId; readonly path: readonly PathSeg[]; readonly constId: string }
  | { readonly rule: 'comprehensionInstantiate'; readonly bubble: RegionId; readonly comp: DiagramWithBoundary }
  | { readonly rule: 'comprehensionAbstract'; readonly wrap: SubgraphSelection; readonly comp: DiagramWithBoundary; readonly occurrences: readonly AbstractionOccurrence[] }
  | { readonly rule: 'theorem'; readonly name: string; readonly at: TheoremApplication; readonly direction: 'forward' | 'reverse' }

export function applyStep(d: Diagram, step: ProofStep, ctx: ProofContext): Diagram {
  switch (step.rule) {
    case 'insertion': return applyInsertion(d, step.region, step.pattern, step.attachments)
    case 'wireJoin': return applyWireJoin(d, step.a, step.b)
    case 'erasure': return applyErasure(d, step.sel)
    case 'wireSever': return applyWireSever(d, step.wire, step.keep)
    case 'iteration': return applyIteration(d, step.sel, step.target)
    case 'deiteration': return applyDeiteration(d, step.sel, step.fuel)
    case 'doubleCutIntro': return applyDoubleCutIntro(d, step.sel)
    case 'doubleCutElim': return applyDoubleCutElim(d, step.region)
    case 'conversion': return applyConversionByCertificate(d, step.node, step.term, step.certificate, step.attachments)
    case 'fusion': return applyFusion(d, step.wire)
    case 'fission': return applyFission(d, step.node, step.path)
    case 'unfold': return applyUnfold(d, ctx.definitions, step.node, step.path)
    case 'fold': return applyFold(d, ctx.definitions, step.node, step.path, step.constId)
    case 'comprehensionInstantiate': return applyComprehensionInstantiate(d, step.bubble, step.comp)
    case 'comprehensionAbstract': return applyComprehensionAbstract(d, step.wrap, step.comp, step.occurrences)
    case 'theorem': {
      const thm = ctx.theorems.get(step.name)
      if (thm === undefined) throw new ProofError(`unknown theorem '${step.name}'`)
      return applyTheorem(d, thm, step.at, step.direction)
    }
  }
}

/** Fold steps over a diagram, naming the failing step on any refusal. */
export function replayProof(start: Diagram, steps: readonly ProofStep[], ctx: ProofContext): Diagram {
  let cur = start
  steps.forEach((s, i) => {
    try {
      cur = applyStep(cur, s, ctx)
    } catch (e) {
      throw new ProofError(`step ${i} (${s.rule}) failed: ${e instanceof Error ? e.message : String(e)}`)
    }
  })
  return cur
}
```

`tests/kernel/proof/theorem.test.ts` (the second Step 1 test file — shown here, after the sources, for reading order only):

```ts
import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../../src/kernel/term/parse'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { mkDiagramWithBoundary } from '../../../src/kernel/diagram/boundary'
import { mkSelection } from '../../../src/kernel/diagram/subgraph/selection'
import { diagramFingerprint } from '../../../src/kernel/diagram/canonical/fingerprint'
import { RuleError } from '../../../src/kernel/rules/error'
import { checkTheorem, applyTheorem } from '../../../src/kernel/proof/theorem'
import type { Theorem } from '../../../src/kernel/proof/theorem'
import type { ProofContext } from '../../../src/kernel/proof/step'
import { ProofError } from '../../../src/kernel/proof/error'

const noConsts = new Set<string>()
const p = (s: string) => parseTerm(s, noConsts)
const ctx: ProofContext = { definitions: {}, theorems: new Map() }

/**
 * The running example: P(x) := x = λa.a, Q(x) := x = λa.λb.a.
 * Theorem dropQ: P(x) ∧ Q(x) ⟹ P(x), proven by one erasure.
 */
function dropQ(): Theorem {
  const l = new DiagramBuilder()
  const lp = l.termNode(l.root, p('\\a. a'))
  const lq = l.termNode(l.root, p('\\a. \\b. a'))
  const lb = l.wire(l.root, [
    { node: lp, port: { kind: 'output' } },
    { node: lq, port: { kind: 'output' } },
  ])
  const lhs = mkDiagramWithBoundary(l.build(), [lb])
  const r = new DiagramBuilder()
  const rp = r.termNode(r.root, p('\\a. a'))
  const rb = r.wire(r.root, [{ node: rp, port: { kind: 'output' } }])
  const rhs = mkDiagramWithBoundary(r.build(), [rb])
  return {
    name: 'dropQ', lhs, rhs,
    steps: [{ rule: 'erasure', sel: { region: lhs.diagram.root, regions: [], nodes: [lq], wires: [] } }],
  }
}

describe('checkTheorem', () => {
  it('accepts a valid proof', () => {
    expect(() => checkTheorem(dropQ(), ctx)).not.toThrow()
  })

  it('rejects proofs that do not arrive at the stated rhs', () => {
    const t = dropQ()
    const broken: Theorem = { ...t, steps: [] }
    expect(() => checkTheorem(broken, ctx))
      .toThrowError(/does not arrive at the stated right-hand side/)
  })

  it('rejects arity mismatches and non-root boundary stubs, by name', () => {
    const t = dropQ()
    const bad: Theorem = { ...t, rhs: mkDiagramWithBoundary(t.rhs.diagram, []) }
    expect(() => checkTheorem(bad, ctx)).toThrowError(/boundary arity mismatch/)

    const n = new DiagramBuilder()
    const cut = n.cut(n.root)
    const nn = n.termNode(cut, p('\\a. a'))
    const nw = n.wire(cut, [{ node: nn, port: { kind: 'output' } }])
    const nonRoot: Theorem = { ...t, lhs: mkDiagramWithBoundary(n.build(), [nw]), steps: [] }
    expect(() => checkTheorem(nonRoot, ctx)).toThrowError(/not scoped at the diagram root/)
  })

  it('rejects proofs that destroy a boundary wire', () => {
    const t = dropQ()
    // erase BOTH nodes: the boundary wire survives as endpoint-less — still
    // exists, so build a destroying case differently: sever... a wire is only
    // DESTROYED by join (inner) or being internal to a removal. Select it
    // explicitly as removal content:
    const destroying: Theorem = {
      ...t,
      steps: [{
        rule: 'erasure',
        sel: {
          region: t.lhs.diagram.root, regions: [],
          nodes: Object.keys(t.lhs.diagram.nodes),
          wires: [t.lhs.boundary[0]!],
        },
      }],
    }
    expect(() => checkTheorem(destroying, ctx)).toThrowError(/boundary wire .* was destroyed/)
  })
})

describe('applyTheorem', () => {
  function host() {
    // host: P(v) ∧ Q(v) ∧ hub(v) at root
    const h = new DiagramBuilder()
    const hp = h.termNode(h.root, p('\\a. a'))
    const hq = h.termNode(h.root, p('\\a. \\b. a'))
    const hub = h.termNode(h.root, p('y'))
    const v = h.wire(h.root, [
      { node: hp, port: { kind: 'output' } },
      { node: hq, port: { kind: 'output' } },
      { node: hub, port: { kind: 'freeVar', name: 'y' } },
    ])
    return { d: h.build(), hp, hq, hub, v }
  }

  it('forward at a positive region rewrites the occurrence in one step', () => {
    const { d, hp, hq, v } = host()
    const out = applyTheorem(d, dropQ(), {
      sel: { region: d.root, regions: [], nodes: [hp, hq], wires: [] },
      args: [v],
    }, 'forward')
    // NOTE: assert by SHAPE, not by id — splice may legitimately REUSE the
    // removed nodes' ids (freshId only dodges ids still present). Expected:
    // the hub plus exactly one spliced P node, both on v.
    expect(Object.values(out.nodes)).toHaveLength(2)
    const eps = out.wires[v]?.endpoints ?? []
    expect(eps).toHaveLength(2)
    expect(eps.filter((ep) => ep.port.kind === 'output')).toHaveLength(1)
    expect(eps.filter((ep) => ep.port.kind === 'freeVar')).toHaveLength(1)
  })

  it('reverse at a negative region strengthens, and round-trips by fingerprint', () => {
    const h = new DiagramBuilder()
    const cut = h.cut(h.root)
    const hp = h.termNode(cut, p('\\a. a'))
    const v = h.wire(cut, [{ node: hp, port: { kind: 'output' } }])
    const d = h.build()
    const strengthened = applyTheorem(d, dropQ(), {
      sel: { region: cut, regions: [], nodes: [hp], wires: [] },
      args: [v],
    }, 'reverse')
    const nodes = Object.entries(strengthened.nodes)
    expect(nodes).toHaveLength(2)
    // applying forward inside the cut is refused (negative)
    const [pid] = nodes.find(([, n]) => n.kind === 'term' && n.term.kind === 'lam' && n.term.body.kind === 'bvar')!
    const [qid] = nodes.find(([id]) => id !== pid)!
    expect(() => applyTheorem(strengthened, dropQ(), {
      sel: { region: cut, regions: [], nodes: [pid, qid], wires: [] },
      args: [v],
    }, 'forward')).toThrowError(/requires a positive region/)
  })

  it('refuses occurrences that do not match the theorem side', () => {
    const { d, hp, v } = host()
    expect(() => applyTheorem(d, dropQ(), {
      sel: { region: d.root, regions: [], nodes: [hp], wires: [] },
      args: [v],
    }, 'forward')).toThrowError(/not an occurrence of theorem 'dropQ'/)
  })

  it('refuses wrong polarity by name in both directions', () => {
    const { d, hp, hq, v } = host()
    let caught: unknown
    try {
      applyTheorem(d, dropQ(), {
        sel: { region: d.root, regions: [], nodes: [hp, hq], wires: [] },
        args: [v],
      }, 'reverse')
    } catch (e) { caught = e }
    expect(caught).toBeInstanceOf(RuleError)
    expect((caught as Error).message).toMatch(/reverse requires a negative region/)
  })
})

describe('theorem steps inside proofs (derived rules used natively)', () => {
  it('a registered theorem applies through replayProof without expansion', () => {
    const t = dropQ()
    const theorems = new Map([[t.name, t]])
    const c2: ProofContext = { definitions: {}, theorems }
    const { d, hp, hq, v } = (() => {
      const h = new DiagramBuilder()
      const hp = h.termNode(h.root, p('\\a. a'))
      const hq = h.termNode(h.root, p('\\a. \\b. a'))
      const v = h.wire(h.root, [
        { node: hp, port: { kind: 'output' } },
        { node: hq, port: { kind: 'output' } },
      ])
      return { d: h.build(), hp, hq, v }
    })()
    const out = replayProof(d, [{
      rule: 'theorem', name: 'dropQ',
      at: { sel: { region: d.root, regions: [], nodes: [hp, hq], wires: [] }, args: [v] },
      direction: 'forward',
    }], c2)
    expect(Object.values(out.nodes)).toHaveLength(1)
  })
})
```

(`replayProof` joins the top-of-file imports: `import { replayProof } from '../../../src/kernel/proof/step'`.)

- [ ] **Step 4: Verify PASS, full suite, typecheck**

- [ ] **Step 5: Commit**

```bash
git add src/kernel/proof/error.ts src/kernel/proof/step.ts src/kernel/proof/theorem.ts tests/kernel/proof/step.test.ts tests/kernel/proof/theorem.test.ts
git commit -m "feat(kernel): proof steps with gate-enforcing replay; theorems as derived rules"
```

**Review outcome (commits `0042bf9`+`7694942`, fix `1c63bae`):** Deep review SOUND. Implementer caught a second plan-test bug (id-brittle assertion; splice may reuse removed ids — assert by shape). Dispatch audit 16/16 with correct argument order; conversion replays by certificate. Probes: six gate-bypass refusals through replayProof with step indices; blank ⟹ T citation via empty selection works both directions; theorem-in-theorem accepted, forged variant refused; boundary destruction via join is structurally unreachable (root-scoped boundary wires are positive-scope; join gates inner-negative) while the erasure route fires /was destroyed/. Mutant ii — UNPINNED fingerprint comparison in checkTheorem, a real argument-order forgery gap — survived and was killed by an arity-2 pin-swap test (`1c63bae`). Noted: hand-rolled Theorem records with phantom boundary wires crash with a TypeError rather than ProofError (loud, no false acceptance; structural-type seam). Suite: 348.

The `src/kernel/proof/theorem.ts` source referenced in Step 3 above:

```ts
import type { Diagram, WireId } from '../diagram/diagram'
import { polarity } from '../diagram/regions'
import type { DiagramWithBoundary } from '../diagram/boundary'
import { mkDiagramWithBoundary } from '../diagram/boundary'
import type { SubgraphSelection } from '../diagram/subgraph/selection'
import { extractSubgraph } from '../diagram/subgraph/extract'
import { removeSubgraph, spliceSubgraph } from '../diagram/subgraph/splice'
import { boundaryFingerprint } from '../diagram/canonical/fingerprint'
import { RuleError } from '../rules/error'
import type { ProofStep, ProofContext } from './step'
import { replayProof } from './step'
import { ProofError } from './error'

export type Theorem = {
  readonly name: string
  readonly lhs: DiagramWithBoundary
  readonly rhs: DiagramWithBoundary
  readonly steps: readonly ProofStep[]
}

export type TheoremApplication = {
  readonly sel: SubgraphSelection
  readonly args: readonly WireId[]
}

/**
 * Verify a theorem once: replay its steps from lhs.diagram (each applier
 * enforcing its own gate) and require the result, pinned by the lhs boundary,
 * to be isomorphic to the stated rhs respecting boundary order. Boundary
 * wires must survive the proof (keep them as the OUTER wire of any join) and
 * must be root-scoped on both sides (splice's stub invariant).
 */
export function checkTheorem(thm: Theorem, ctx: ProofContext): void {
  if (thm.lhs.boundary.length !== thm.rhs.boundary.length) {
    throw new ProofError(
      `theorem '${thm.name}': boundary arity mismatch (lhs ${thm.lhs.boundary.length}, rhs ${thm.rhs.boundary.length})`,
    )
  }
  for (const side of [thm.lhs, thm.rhs]) {
    for (const w of side.boundary) {
      if (side.diagram.wires[w]!.scope !== side.diagram.root) {
        throw new ProofError(`theorem '${thm.name}': boundary wire '${w}' is not scoped at the diagram root`)
      }
    }
  }
  const result = replayProof(thm.lhs.diagram, thm.steps, ctx)
  for (const w of thm.lhs.boundary) {
    if (result.wires[w] === undefined) {
      throw new ProofError(`theorem '${thm.name}': boundary wire '${w}' was destroyed by the proof`)
    }
  }
  const got = boundaryFingerprint(mkDiagramWithBoundary(result, thm.lhs.boundary))
  if (got !== boundaryFingerprint(thm.rhs)) {
    throw new ProofError(`theorem '${thm.name}': the proof does not arrive at the stated right-hand side`)
  }
}

/**
 * The derived-rule application (justify once, apply natively — the stored
 * proof is NEVER inlined): rewrite a verified occurrence of one theorem side
 * into the other. Forward (lhs→rhs) is sound at POSITIVE regions, reverse
 * (rhs→lhs) at NEGATIVE regions, by monotonicity. The occurrence is checked
 * exactly — extract, reorder its boundary by args, compare pinned
 * fingerprints — the same machinery as comprehension abstraction.
 */
export function applyTheorem(
  d: Diagram,
  thm: Theorem,
  at: TheoremApplication,
  direction: 'forward' | 'reverse',
): Diagram {
  const from = direction === 'forward' ? thm.lhs : thm.rhs
  const to = direction === 'forward' ? thm.rhs : thm.lhs
  const need = direction === 'forward' ? 'positive' : 'negative'
  const have = polarity(d, at.sel.region)
  if (have !== need) {
    throw new RuleError(
      `theorem '${thm.name}' applied ${direction} requires a ${need} region; '${at.sel.region}' is ${have}`,
    )
  }
  const { pattern, attachments } = extractSubgraph(d, at.sel)
  if (at.args.length !== attachments.length) {
    throw new RuleError(
      `the selection has ${attachments.length} attachment wires but theorem '${thm.name}' takes ${at.args.length} arguments here`,
    )
  }
  if (new Set(at.args).size !== at.args.length) {
    throw new RuleError(`theorem argument wires are not distinct`)
  }
  const reordered = at.args.map((a) => {
    const j = attachments.indexOf(a)
    if (j === -1) throw new RuleError(`argument wire '${a}' is not an attachment wire of the selection`)
    return pattern.boundary[j]!
  })
  if (boundaryFingerprint(mkDiagramWithBoundary(pattern.diagram, reordered)) !== boundaryFingerprint(from)) {
    throw new RuleError(
      `the selection is not an occurrence of theorem '${thm.name}' ${direction === 'forward' ? 'left' : 'right'}-hand side`,
    )
  }
  const removed = removeSubgraph(d, at.sel)
  return spliceSubgraph(removed, at.sel.region, to, at.args)
}
```

---

### Task 3: Meet-in-the-middle composition

**Files:**
- Create: `src/kernel/proof/compose.ts`
- Test: `tests/kernel/proof/compose.test.ts`

- [ ] **Step 1: Write the failing tests**

`tests/kernel/proof/compose.test.ts`:

```ts
import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../../src/kernel/term/parse'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { mkSelection } from '../../../src/kernel/diagram/subgraph/selection'
import { diagramFingerprint } from '../../../src/kernel/diagram/canonical/fingerprint'
import { replayProof } from '../../../src/kernel/proof/step'
import type { ProofContext, ProofStep } from '../../../src/kernel/proof/step'
import { composeProofs } from '../../../src/kernel/proof/compose'

const noConsts = new Set<string>()
const p = (s: string) => parseTerm(s, noConsts)
const ctx: ProofContext = { definitions: {}, theorems: new Map() }

/** Two independently built, differently-id'd copies of the same diagram. */
function twoCopies() {
  const a = new DiagramBuilder()
  const an = a.termNode(a.root, p('y'))
  const ahub = a.termNode(a.root, p('\\x. x'))
  a.wire(a.root, [
    { node: an, port: { kind: 'freeVar', name: 'y' } },
    { node: ahub, port: { kind: 'output' } },
  ])
  const b = new DiagramBuilder()
  // build in a DIFFERENT order so ids differ structurally
  const bhub = b.termNode(b.root, p('\\x. x'))
  const bn = b.termNode(b.root, p('y'))
  b.wire(b.root, [
    { node: bn, port: { kind: 'freeVar', name: 'y' } },
    { node: bhub, port: { kind: 'output' } },
  ])
  return { da: a.build(), db: b.build(), bn }
}

describe('composeProofs', () => {
  it('rewrites a backward tail onto the forward meet and replays end to end', () => {
    const { da, db, bn } = twoCopies()
    // backward tail (recorded against db): wrap the y-node in a double cut
    const tail: ProofStep[] = [{
      rule: 'doubleCutIntro',
      sel: mkSelection(db, { region: db.root, regions: [], nodes: [bn], wires: [] }),
    }]
    const composed = composeProofs(da, db, tail, ctx)
    const viaA = replayProof(da, composed, ctx)
    const viaB = replayProof(db, tail, ctx)
    expect(diagramFingerprint(viaA)).toBe(diagramFingerprint(viaB))
  })

  it('handles multi-step tails whose later steps reference ids created by earlier ones', () => {
    const { da, db, bn } = twoCopies()
    const wrapped = replayProof(db, [{
      rule: 'doubleCutIntro',
      sel: mkSelection(db, { region: db.root, regions: [], nodes: [bn], wires: [] }),
    }], ctx)
    // find the new outer cut in the b-side result, then eliminate it again
    const outer = Object.entries(wrapped.regions)
      .find(([id, r]) => r.kind === 'cut' && db.regions[id] === undefined && r.parent === db.root)![0]
    const tail: ProofStep[] = [
      { rule: 'doubleCutIntro', sel: mkSelection(db, { region: db.root, regions: [], nodes: [bn], wires: [] }) },
      { rule: 'doubleCutElim', region: outer },
    ]
    const composed = composeProofs(da, db, tail, ctx)
    const viaA = replayProof(da, composed, ctx)
    expect(diagramFingerprint(viaA)).toBe(diagramFingerprint(da))
  })

  it('works across automorphic diagrams (two identical nodes)', () => {
    const mk = () => {
      const h = new DiagramBuilder()
      const n1 = h.termNode(h.root, p('\\x. x'))
      h.termNode(h.root, p('\\x. x'))
      return { d: h.build(), n1 }
    }
    const { d: da } = mk()
    const { d: db, n1: bn1 } = mk()
    const tail: ProofStep[] = [{
      rule: 'erasure',
      sel: mkSelection(db, { region: db.root, regions: [], nodes: [bn1], wires: [] }),
    }]
    const composed = composeProofs(da, db, tail, ctx)
    const viaA = replayProof(da, composed, ctx)
    expect(Object.values(viaA.nodes)).toHaveLength(1)
  })

  it('refuses non-isomorphic meets by name', () => {
    const { da } = twoCopies()
    const other = new DiagramBuilder()
    other.termNode(other.root, p('y'))
    expect(() => composeProofs(da, other.build(), [], ctx))
      .toThrowError(/do not meet/)
  })
})
```

- [ ] **Step 2: Run tests to verify they fail**

Run: `npx vitest run tests/kernel/proof/compose.test.ts`
Expected: FAIL — cannot resolve `proof/compose`.

- [ ] **Step 3: Implement**

`src/kernel/proof/compose.ts`:

```ts
import type { Diagram, Endpoint, WireId } from '../diagram/diagram'
import type { DiagramIso } from '../diagram/canonical/iso'
import { isoBetween } from '../diagram/canonical/iso'
import type { SubgraphSelection } from '../diagram/subgraph/selection'
import type { AbstractionOccurrence } from '../rules/comprehension'
import type { ProofContext, ProofStep } from './step'
import { applyStep } from './step'
import { ProofError } from './error'

function mapId<T extends string>(m: ReadonlyMap<string, string>, id: T, what: string): T {
  const img = m.get(id)
  if (img === undefined) throw new ProofError(`composition cannot map ${what} '${id}': not present at the meet`)
  return img as T
}

function mapSel(iso: DiagramIso, sel: SubgraphSelection): SubgraphSelection {
  return {
    region: mapId(iso.regions, sel.region, 'region'),
    regions: sel.regions.map((r) => mapId(iso.regions, r, 'region')),
    nodes: sel.nodes.map((n) => mapId(iso.nodes, n, 'node')),
    wires: sel.wires.map((w) => mapId(iso.wires, w, 'wire')),
  }
}

function mapEndpoint(iso: DiagramIso, ep: Endpoint): Endpoint {
  return { node: mapId(iso.nodes, ep.node, 'node'), port: ep.port }
}

function mapOccurrence(iso: DiagramIso, occ: AbstractionOccurrence): AbstractionOccurrence {
  return { sel: mapSel(iso, occ.sel), args: occ.args.map((w) => mapId(iso.wires, w, 'wire')) }
}

/**
 * Rewrite one step's HOST ids through an isomorphism. Embedded patterns
 * (DiagramWithBoundary values) are self-contained namespaces and terms are
 * port-name-internal — neither is mapped.
 */
export function mapStepIds(step: ProofStep, iso: DiagramIso): ProofStep {
  switch (step.rule) {
    case 'insertion':
      return { ...step, region: mapId(iso.regions, step.region, 'region'), attachments: step.attachments.map((w) => mapId(iso.wires, w, 'wire')) }
    case 'wireJoin':
      return { ...step, a: mapId(iso.wires, step.a, 'wire'), b: mapId(iso.wires, step.b, 'wire') }
    case 'erasure':
      return { ...step, sel: mapSel(iso, step.sel) }
    case 'wireSever':
      return { ...step, wire: mapId(iso.wires, step.wire, 'wire'), keep: step.keep.map((ep) => mapEndpoint(iso, ep)) }
    case 'iteration':
      return { ...step, sel: mapSel(iso, step.sel), target: mapId(iso.regions, step.target, 'region') }
    case 'deiteration':
      return { ...step, sel: mapSel(iso, step.sel) }
    case 'doubleCutIntro':
      return { ...step, sel: mapSel(iso, step.sel) }
    case 'doubleCutElim':
      return { ...step, region: mapId(iso.regions, step.region, 'region') }
    case 'conversion': {
      const attachments: Record<string, WireId> = {}
      for (const [name, w] of Object.entries(step.attachments)) attachments[name] = mapId(iso.wires, w, 'wire')
      return { ...step, node: mapId(iso.nodes, step.node, 'node'), attachments }
    }
    case 'fusion':
      return { ...step, wire: mapId(iso.wires, step.wire, 'wire') }
    case 'fission':
      return { ...step, node: mapId(iso.nodes, step.node, 'node') }
    case 'unfold':
      return { ...step, node: mapId(iso.nodes, step.node, 'node') }
    case 'fold':
      return { ...step, node: mapId(iso.nodes, step.node, 'node') }
    case 'comprehensionInstantiate':
      return { ...step, bubble: mapId(iso.regions, step.bubble, 'region') }
    case 'comprehensionAbstract':
      return { ...step, wrap: mapSel(iso, step.wrap), occurrences: step.occurrences.map((o) => mapOccurrence(iso, o)) }
    case 'theorem':
      return { ...step, at: { sel: mapSel(iso, step.at.sel), args: step.at.args.map((w) => mapId(iso.wires, w, 'wire')) } }
  }
}

/**
 * Meet-in-the-middle: transplant a tail of steps recorded against
 * `meetSource` onto the isomorphic `meetTarget`. Fresh ids minted during
 * replay depend on the id environment, so a single up-front rewrite cannot
 * work — instead the isomorphism is re-derived from canonical labelings
 * after every step (appliers are iso-equivariant up to fresh-id choice).
 */
export function composeProofs(
  meetTarget: Diagram,
  meetSource: Diagram,
  tail: readonly ProofStep[],
  ctx: ProofContext,
): ProofStep[] {
  let iso = isoBetween(meetSource, meetTarget)
  if (iso === null) throw new ProofError('the two sides do not meet: the diagrams are not isomorphic')
  let curTarget = meetTarget
  let curSource = meetSource
  const out: ProofStep[] = []
  for (const [i, step] of tail.entries()) {
    const mapped = mapStepIds(step, iso)
    out.push(mapped)
    try {
      curTarget = applyStep(curTarget, mapped, ctx)
      curSource = applyStep(curSource, step, ctx)
    } catch (e) {
      throw new ProofError(`composing step ${i} (${step.rule}) failed: ${e instanceof Error ? e.message : String(e)}`)
    }
    iso = isoBetween(curSource, curTarget)
    if (iso === null) {
      throw new ProofError(`composing step ${i} (${step.rule}) diverged: the sides are no longer isomorphic`)
    }
  }
  return out
}
```

- [ ] **Step 4: Verify PASS, full suite, typecheck**

- [ ] **Step 5: Commit**

```bash
git add src/kernel/proof/compose.ts tests/kernel/proof/compose.test.ts
git commit -m "feat(kernel): meet-in-the-middle proof composition via canonical isomorphisms"
```

**Review outcome (commit `59ef0f9`, fix `9f8f6cf`):** APPROVED; byte-identical to plan. mapStepIds exhaustiveness audited 16/16 field-by-field (attachment VALUES mapped, port-name keys/terms/embedded patterns deliberately not). Probes: insertion into a mid-tail fresh region maps through the re-derived iso; theorem steps map sel+args; automorphic meets compose; failure paths throw without partial output. Mutant iii (erasure unmapped) survived the symmetric battery — killed by an asymmetric-ids test (`9f8f6cf`). Divergence guard kept as defense-in-depth (reachable only under applier bugs, demonstrated by mutant ii). Suite: 353.

---

### Task 4: Proof serialization

**Files:**
- Modify: `src/kernel/diagram/json.ts` (export `parsePortKey`)
- Create: `src/kernel/proof/json.ts`
- Test: `tests/kernel/proof/json.test.ts`

- [ ] **Step 1: Write the failing tests**

`tests/kernel/proof/json.test.ts`:

```ts
import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../../src/kernel/term/parse'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { mkDiagramWithBoundary } from '../../../src/kernel/diagram/boundary'
import { applyConversion } from '../../../src/kernel/rules/conversion'
import type { ProofStep } from '../../../src/kernel/proof/step'
import { stepToJson, stepFromJson, theoremToJson, theoremFromJson } from '../../../src/kernel/proof/json'
import type { Theorem } from '../../../src/kernel/proof/theorem'

const noConsts = new Set<string>()
const p = (s: string) => parseTerm(s, noConsts)

function roundTrip(s: ProofStep): void {
  const j = JSON.parse(JSON.stringify(stepToJson(s)))
  expect(stepFromJson(j)).toEqual(s)
}

describe('step round-trips through JSON', () => {
  it('covers every step kind', () => {
    const b = new DiagramBuilder()
    const bn = b.termNode(b.root, p('\\x. x'))
    const bw = b.wire(b.root, [{ node: bn, port: { kind: 'output' } }])
    const pat = mkDiagramWithBoundary(b.build(), [bw])

    const h = new DiagramBuilder()
    const n = h.termNode(h.root, p('(\\x. x) y'))
    const d = h.build()
    const { certificate } = applyConversion(d, n, p('y'), 10)

    const sel = { region: 'r0', regions: ['r1'], nodes: ['n0'], wires: ['w0'] }
    const steps: ProofStep[] = [
      { rule: 'insertion', region: 'r1', pattern: pat, attachments: ['w0'] },
      { rule: 'wireJoin', a: 'w0', b: 'w1' },
      { rule: 'erasure', sel },
      { rule: 'wireSever', wire: 'w0', keep: [{ node: 'n0', port: { kind: 'freeVar', name: 'y' } }] },
      { rule: 'iteration', sel, target: 'r1' },
      { rule: 'deiteration', sel, fuel: 50 },
      { rule: 'doubleCutIntro', sel },
      { rule: 'doubleCutElim', region: 'r1' },
      { rule: 'conversion', node: 'n0', term: p('y'), certificate, attachments: { z: 'w0' } },
      { rule: 'fusion', wire: 'w0' },
      { rule: 'fission', node: 'n0', path: ['fn', 'arg'] },
      { rule: 'unfold', node: 'n0', path: [] },
      { rule: 'fold', node: 'n0', path: ['body'], constId: 'I' },
      { rule: 'comprehensionInstantiate', bubble: 'r1', comp: pat },
      { rule: 'comprehensionAbstract', wrap: sel, comp: pat, occurrences: [{ sel, args: ['w0'] }] },
      { rule: 'theorem', name: 'dropQ', at: { sel, args: ['w0'] }, direction: 'reverse' },
    ]
    for (const s of steps) roundTrip(s)
  })

  it('rejects malformed steps loudly', () => {
    expect(() => stepFromJson({ rule: 'nonsense' })).toThrowError(/malformed proof JSON/)
    expect(() => stepFromJson({ rule: 'erasure', sel: { region: 'r0', regions: [], nodes: [], wires: [] }, extra: 1 }))
      .toThrowError(/unknown field 'extra'/)
    expect(() => stepFromJson({ rule: 'fission', node: 'n0', path: ['sideways'] }))
      .toThrowError(/path segment/)
    expect(() => stepFromJson({ rule: 'deiteration', sel: { region: 'r0', regions: [], nodes: [], wires: [] }, fuel: -1 }))
      .toThrowError(/fuel/)
  })
})

describe('theorem round-trips through JSON', () => {
  it('preserves sides, boundary order, and steps', () => {
    const l = new DiagramBuilder()
    const lp = l.termNode(l.root, p('\\a. a'))
    const lb = l.wire(l.root, [{ node: lp, port: { kind: 'output' } }])
    const side = mkDiagramWithBoundary(l.build(), [lb])
    const t: Theorem = {
      name: 'noop', lhs: side, rhs: side,
      steps: [{ rule: 'doubleCutIntro', sel: { region: side.diagram.root, regions: [], nodes: [], wires: [] } },
              { rule: 'doubleCutElim', region: 'dc' }],
    }
    const j = JSON.parse(JSON.stringify(theoremToJson(t)))
    const back = theoremFromJson(j)
    expect(back.name).toBe('noop')
    expect(back.lhs.boundary).toEqual([lb])
    expect(back.steps).toEqual(t.steps)
  })
})
```

- [ ] **Step 2: Run tests to verify they fail**

Run: `npx vitest run tests/kernel/proof/json.test.ts`
Expected: FAIL — cannot resolve `proof/json`.

- [ ] **Step 3: Implement**

In `src/kernel/diagram/json.ts`, change `function parsePortKey` to `export function parsePortKey` (no other changes).

`src/kernel/proof/json.ts`:

```ts
import type { Term } from '../term/term'
import { serializeTerm, deserializeTerm } from '../term/serialize'
import type { PathSeg, ReductionStep } from '../term/reduce'
import type { ConversionCertificate } from '../term/certificate'
import type { Endpoint, WireId } from '../diagram/diagram'
import { portKey } from '../diagram/diagram'
import { diagramToJson, diagramFromJson, parsePortKey } from '../diagram/json'
import type { DiagramWithBoundary } from '../diagram/boundary'
import { mkDiagramWithBoundary } from '../diagram/boundary'
import type { SubgraphSelection } from '../diagram/subgraph/selection'
import type { AbstractionOccurrence } from '../rules/comprehension'
import type { ProofStep } from './step'
import type { Theorem, TheoremApplication } from './theorem'

function fail(msg: string): never {
  throw new Error(`malformed proof JSON: ${msg}`)
}

function isRecord(v: unknown): v is Record<string, unknown> {
  return typeof v === 'object' && v !== null && !Array.isArray(v)
}

function assertOnlyKeys(v: Record<string, unknown>, allowed: readonly string[], what: string): void {
  for (const k of Object.keys(v)) {
    if (!allowed.includes(k)) fail(`${what} has unknown field '${k}'`)
  }
}

function str(v: unknown, what: string): string {
  if (typeof v !== 'string') fail(`${what} must be a string`)
  return v
}

function strArray(v: unknown, what: string): string[] {
  if (!Array.isArray(v)) fail(`${what} must be an array`)
  return v.map((x, i) => str(x, `${what}[${i}]`))
}

function pathFromJson(v: unknown, what: string): PathSeg[] {
  return strArray(v, what).map((s, i) => {
    if (s === 'body' || s === 'fn' || s === 'arg') return s
    return fail(`${what}[${i}] is not a path segment (body|fn|arg): '${s}'`)
  })
}

function termFromJson(v: unknown, what: string): Term {
  try {
    return deserializeTerm(str(v, what))
  } catch (e) {
    return fail(`${what}: ${e instanceof Error ? e.message : String(e)}`)
  }
}

function selToJson(s: SubgraphSelection): unknown {
  return { region: s.region, regions: [...s.regions], nodes: [...s.nodes], wires: [...s.wires] }
}

function selFromJson(v: unknown, what: string): SubgraphSelection {
  if (!isRecord(v)) fail(`${what} must be an object`)
  assertOnlyKeys(v, ['region', 'regions', 'nodes', 'wires'], what)
  return {
    region: str(v.region, `${what}.region`),
    regions: strArray(v.regions, `${what}.regions`),
    nodes: strArray(v.nodes, `${what}.nodes`),
    wires: strArray(v.wires, `${what}.wires`),
  }
}

function endpointToJson(ep: Endpoint): unknown {
  return { node: ep.node, port: portKey(ep.port) }
}

function endpointFromJson(v: unknown, what: string): Endpoint {
  if (!isRecord(v)) fail(`${what} must be an object`)
  assertOnlyKeys(v, ['node', 'port'], what)
  return { node: str(v.node, `${what}.node`), port: parsePortKey(str(v.port, `${what}.port`)) }
}

export function dwbToJson(dwb: DiagramWithBoundary): unknown {
  return { diagram: diagramToJson(dwb.diagram), boundary: [...dwb.boundary] }
}

export function dwbFromJson(v: unknown, what = 'pattern'): DiagramWithBoundary {
  if (!isRecord(v)) fail(`${what} must be an object`)
  assertOnlyKeys(v, ['diagram', 'boundary'], what)
  return mkDiagramWithBoundary(diagramFromJson(v.diagram), strArray(v.boundary, `${what}.boundary`))
}

function certToJson(c: ConversionCertificate): unknown {
  const steps = (xs: readonly ReductionStep[]) => xs.map((s) => ({ kind: s.kind, path: [...s.path] }))
  return { leftSteps: steps(c.leftSteps), rightSteps: steps(c.rightSteps) }
}

function certFromJson(v: unknown, what: string): ConversionCertificate {
  if (!isRecord(v)) fail(`${what} must be an object`)
  assertOnlyKeys(v, ['leftSteps', 'rightSteps'], what)
  const steps = (xs: unknown, w: string): ReductionStep[] => {
    if (!Array.isArray(xs)) fail(`${w} must be an array`)
    return xs.map((x, i) => {
      if (!isRecord(x)) fail(`${w}[${i}] must be an object`)
      assertOnlyKeys(x, ['kind', 'path'], `${w}[${i}]`)
      const kind = str(x.kind, `${w}[${i}].kind`)
      if (kind !== 'beta' && kind !== 'eta') fail(`${w}[${i}].kind must be beta|eta`)
      return { kind, path: pathFromJson(x.path, `${w}[${i}].path`) }
    })
  }
  return { leftSteps: steps(v.leftSteps, `${what}.leftSteps`), rightSteps: steps(v.rightSteps, `${what}.rightSteps`) }
}

function occToJson(o: AbstractionOccurrence): unknown {
  return { sel: selToJson(o.sel), args: [...o.args] }
}

function occFromJson(v: unknown, what: string): AbstractionOccurrence {
  if (!isRecord(v)) fail(`${what} must be an object`)
  assertOnlyKeys(v, ['sel', 'args'], what)
  return { sel: selFromJson(v.sel, `${what}.sel`), args: strArray(v.args, `${what}.args`) }
}

function appToJson(a: TheoremApplication): unknown {
  return { sel: selToJson(a.sel), args: [...a.args] }
}

function appFromJson(v: unknown, what: string): TheoremApplication {
  if (!isRecord(v)) fail(`${what} must be an object`)
  assertOnlyKeys(v, ['sel', 'args'], what)
  return { sel: selFromJson(v.sel, `${what}.sel`), args: strArray(v.args, `${what}.args`) }
}

export function stepToJson(s: ProofStep): unknown {
  switch (s.rule) {
    case 'insertion':
      return { rule: s.rule, region: s.region, pattern: dwbToJson(s.pattern), attachments: [...s.attachments] }
    case 'wireJoin':
      return { rule: s.rule, a: s.a, b: s.b }
    case 'erasure':
      return { rule: s.rule, sel: selToJson(s.sel) }
    case 'wireSever':
      return { rule: s.rule, wire: s.wire, keep: s.keep.map(endpointToJson) }
    case 'iteration':
      return { rule: s.rule, sel: selToJson(s.sel), target: s.target }
    case 'deiteration':
      return { rule: s.rule, sel: selToJson(s.sel), fuel: s.fuel }
    case 'doubleCutIntro':
      return { rule: s.rule, sel: selToJson(s.sel) }
    case 'doubleCutElim':
      return { rule: s.rule, region: s.region }
    case 'conversion':
      return { rule: s.rule, node: s.node, term: serializeTerm(s.term), certificate: certToJson(s.certificate), attachments: { ...s.attachments } }
    case 'fusion':
      return { rule: s.rule, wire: s.wire }
    case 'fission':
      return { rule: s.rule, node: s.node, path: [...s.path] }
    case 'unfold':
      return { rule: s.rule, node: s.node, path: [...s.path] }
    case 'fold':
      return { rule: s.rule, node: s.node, path: [...s.path], constId: s.constId }
    case 'comprehensionInstantiate':
      return { rule: s.rule, bubble: s.bubble, comp: dwbToJson(s.comp) }
    case 'comprehensionAbstract':
      return { rule: s.rule, wrap: selToJson(s.wrap), comp: dwbToJson(s.comp), occurrences: s.occurrences.map(occToJson) }
    case 'theorem':
      return { rule: s.rule, name: s.name, at: appToJson(s.at), direction: s.direction }
  }
}

export function stepFromJson(j: unknown): ProofStep {
  if (!isRecord(j)) fail('step must be an object')
  const rule = str(j.rule, 'step.rule')
  switch (rule) {
    case 'insertion':
      assertOnlyKeys(j, ['rule', 'region', 'pattern', 'attachments'], 'insertion step')
      return { rule, region: str(j.region, 'region'), pattern: dwbFromJson(j.pattern), attachments: strArray(j.attachments, 'attachments') }
    case 'wireJoin':
      assertOnlyKeys(j, ['rule', 'a', 'b'], 'wireJoin step')
      return { rule, a: str(j.a, 'a'), b: str(j.b, 'b') }
    case 'erasure':
      assertOnlyKeys(j, ['rule', 'sel'], 'erasure step')
      return { rule, sel: selFromJson(j.sel, 'sel') }
    case 'wireSever': {
      assertOnlyKeys(j, ['rule', 'wire', 'keep'], 'wireSever step')
      if (!Array.isArray(j.keep)) fail('keep must be an array')
      return { rule, wire: str(j.wire, 'wire'), keep: j.keep.map((k, i) => endpointFromJson(k, `keep[${i}]`)) }
    }
    case 'iteration':
      assertOnlyKeys(j, ['rule', 'sel', 'target'], 'iteration step')
      return { rule, sel: selFromJson(j.sel, 'sel'), target: str(j.target, 'target') }
    case 'deiteration': {
      assertOnlyKeys(j, ['rule', 'sel', 'fuel'], 'deiteration step')
      if (typeof j.fuel !== 'number' || !Number.isInteger(j.fuel) || j.fuel <= 0) fail('fuel must be a positive integer')
      return { rule, sel: selFromJson(j.sel, 'sel'), fuel: j.fuel }
    }
    case 'doubleCutIntro':
      assertOnlyKeys(j, ['rule', 'sel'], 'doubleCutIntro step')
      return { rule, sel: selFromJson(j.sel, 'sel') }
    case 'doubleCutElim':
      assertOnlyKeys(j, ['rule', 'region'], 'doubleCutElim step')
      return { rule, region: str(j.region, 'region') }
    case 'conversion': {
      assertOnlyKeys(j, ['rule', 'node', 'term', 'certificate', 'attachments'], 'conversion step')
      if (!isRecord(j.attachments)) fail('attachments must be an object')
      const attachments: Record<string, WireId> = {}
      for (const [k, v] of Object.entries(j.attachments)) attachments[k] = str(v, `attachments['${k}']`)
      return { rule, node: str(j.node, 'node'), term: termFromJson(j.term, 'term'), certificate: certFromJson(j.certificate, 'certificate'), attachments }
    }
    case 'fusion':
      assertOnlyKeys(j, ['rule', 'wire'], 'fusion step')
      return { rule, wire: str(j.wire, 'wire') }
    case 'fission':
      assertOnlyKeys(j, ['rule', 'node', 'path'], 'fission step')
      return { rule, node: str(j.node, 'node'), path: pathFromJson(j.path, 'path') }
    case 'unfold':
      assertOnlyKeys(j, ['rule', 'node', 'path'], 'unfold step')
      return { rule, node: str(j.node, 'node'), path: pathFromJson(j.path, 'path') }
    case 'fold':
      assertOnlyKeys(j, ['rule', 'node', 'path', 'constId'], 'fold step')
      return { rule, node: str(j.node, 'node'), path: pathFromJson(j.path, 'path'), constId: str(j.constId, 'constId') }
    case 'comprehensionInstantiate':
      assertOnlyKeys(j, ['rule', 'bubble', 'comp'], 'comprehensionInstantiate step')
      return { rule, bubble: str(j.bubble, 'bubble'), comp: dwbFromJson(j.comp, 'comp') }
    case 'comprehensionAbstract': {
      assertOnlyKeys(j, ['rule', 'wrap', 'comp', 'occurrences'], 'comprehensionAbstract step')
      if (!Array.isArray(j.occurrences)) fail('occurrences must be an array')
      return { rule, wrap: selFromJson(j.wrap, 'wrap'), comp: dwbFromJson(j.comp, 'comp'), occurrences: j.occurrences.map((o, i) => occFromJson(o, `occurrences[${i}]`)) }
    }
    case 'theorem': {
      assertOnlyKeys(j, ['rule', 'name', 'at', 'direction'], 'theorem step')
      const direction = str(j.direction, 'direction')
      if (direction !== 'forward' && direction !== 'reverse') fail("direction must be 'forward'|'reverse'")
      return { rule, name: str(j.name, 'name'), at: appFromJson(j.at, 'at'), direction }
    }
    default:
      return fail(`unknown rule '${rule}'`)
  }
}

export function theoremToJson(t: Theorem): unknown {
  return { name: t.name, lhs: dwbToJson(t.lhs), rhs: dwbToJson(t.rhs), steps: t.steps.map(stepToJson) }
}

export function theoremFromJson(j: unknown): Theorem {
  if (!isRecord(j)) fail('theorem must be an object')
  assertOnlyKeys(j, ['name', 'lhs', 'rhs', 'steps'], 'theorem')
  if (!Array.isArray(j.steps)) fail('theorem.steps must be an array')
  return {
    name: str(j.name, 'theorem.name'),
    lhs: dwbFromJson(j.lhs, 'theorem.lhs'),
    rhs: dwbFromJson(j.rhs, 'theorem.rhs'),
    steps: j.steps.map((s) => stepFromJson(s)),
  }
}
```

- [ ] **Step 4: Verify PASS, full suite, typecheck**

- [ ] **Step 5: Commit**

```bash
git add src/kernel/diagram/json.ts src/kernel/proof/json.ts tests/kernel/proof/json.test.ts
git commit -m "feat(kernel): proof and theorem JSON serialization with strict validation"
```

---

### Task 5: Theory store

**Files:**
- Create: `src/kernel/proof/store.ts`
- Test: `tests/kernel/proof/store.test.ts`

- [ ] **Step 1: Write the failing tests**

`tests/kernel/proof/store.test.ts`:

```ts
import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../../src/kernel/term/parse'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { mkDiagramWithBoundary } from '../../../src/kernel/diagram/boundary'
import type { Theorem } from '../../../src/kernel/proof/theorem'
import type { Theory } from '../../../src/kernel/proof/store'
import { verifyTheory, theoryToJson, loadTheory } from '../../../src/kernel/proof/store'
import { ProofError } from '../../../src/kernel/proof/error'

const noConsts = new Set<string>()
const p = (s: string) => parseTerm(s, noConsts)

function dropQ(): Theorem {
  const l = new DiagramBuilder()
  const lp = l.termNode(l.root, p('\\a. a'))
  const lq = l.termNode(l.root, p('\\a. \\b. a'))
  const lb = l.wire(l.root, [
    { node: lp, port: { kind: 'output' } },
    { node: lq, port: { kind: 'output' } },
  ])
  const lhs = mkDiagramWithBoundary(l.build(), [lb])
  const r = new DiagramBuilder()
  const rp = r.termNode(r.root, p('\\a. a'))
  const rb = r.wire(r.root, [{ node: rp, port: { kind: 'output' } }])
  const rhs = mkDiagramWithBoundary(r.build(), [rb])
  return {
    name: 'dropQ', lhs, rhs,
    steps: [{ rule: 'erasure', sel: { region: lhs.diagram.root, regions: [], nodes: [lq], wires: [] } }],
  }
}

function isIdentity() {
  const b = new DiagramBuilder()
  const n = b.termNode(b.root, p('\\x. x'))
  const w = b.wire(b.root, [{ node: n, port: { kind: 'output' } }])
  return mkDiagramWithBoundary(b.build(), [w])
}

describe('verifyTheory', () => {
  it('verifies definitions, relations, theorems in order and returns the context', () => {
    const theory: Theory = {
      definitions: { I: p('\\x. x') },
      relations: { isIdentity: isIdentity() },
      theorems: [dropQ()],
    }
    const ctx = verifyTheory(theory)
    expect(ctx.theorems.has('dropQ')).toBe(true)
  })

  it('rejects duplicate theorem names and broken proofs, by name', () => {
    const t = dropQ()
    expect(() => verifyTheory({ definitions: {}, relations: {}, theorems: [t, t] }))
      .toThrowError(/duplicate theorem name 'dropQ'/)
    const broken: Theorem = { ...t, steps: [] }
    let caught: unknown
    try { verifyTheory({ definitions: {}, relations: {}, theorems: [broken] }) } catch (e) { caught = e }
    expect(caught).toBeInstanceOf(ProofError)
  })

  it('later theorems may use earlier ones, not vice versa', () => {
    const base = dropQ()
    // derived: applies dropQ inside its own proof
    const l = new DiagramBuilder()
    const lp = l.termNode(l.root, p('\\a. a'))
    const lq = l.termNode(l.root, p('\\a. \\b. a'))
    const lb = l.wire(l.root, [
      { node: lp, port: { kind: 'output' } },
      { node: lq, port: { kind: 'output' } },
    ])
    const lhs = mkDiagramWithBoundary(l.build(), [lb])
    const r = new DiagramBuilder()
    const rp = r.termNode(r.root, p('\\a. a'))
    const rb = r.wire(r.root, [{ node: rp, port: { kind: 'output' } }])
    const rhs = mkDiagramWithBoundary(r.build(), [rb])
    const derived: Theorem = {
      name: 'viaDropQ', lhs, rhs,
      steps: [{
        rule: 'theorem', name: 'dropQ',
        at: { sel: { region: lhs.diagram.root, regions: [], nodes: [lp, lq], wires: [] }, args: [lb] },
        direction: 'forward',
      }],
    }
    expect(() => verifyTheory({ definitions: {}, relations: {}, theorems: [base, derived] })).not.toThrow()
    expect(() => verifyTheory({ definitions: {}, relations: {}, theorems: [derived, base] }))
      .toThrowError(/unknown theorem 'dropQ'/)
  })
})

describe('theory files', () => {
  it('round-trips through JSON with verification on load', () => {
    const theory: Theory = {
      definitions: { I: p('\\x. x') },
      relations: { isIdentity: isIdentity() },
      theorems: [dropQ()],
    }
    const text = JSON.stringify(theoryToJson(theory))
    const { theory: back, ctx } = loadTheory(JSON.parse(text))
    expect(ctx.theorems.has('dropQ')).toBe(true)
    expect(JSON.stringify(theoryToJson(back))).toBe(text)
  })

  it('rejects unversioned or alien envelopes', () => {
    expect(() => loadTheory({ format: 'something-else', version: 1, definitions: {}, relations: {}, theorems: [] }))
      .toThrowError(/format/)
    expect(() => loadTheory({ format: 'visual-proof-theory', version: 99, definitions: {}, relations: {}, theorems: [] }))
      .toThrowError(/version/)
  })
})
```

- [ ] **Step 2: Run tests to verify they fail**

Run: `npx vitest run tests/kernel/proof/store.test.ts`
Expected: FAIL — cannot resolve `proof/store`.

- [ ] **Step 3: Implement**

`src/kernel/proof/store.ts`:

```ts
import type { Term } from '../term/term'
import { serializeTerm, deserializeTerm } from '../term/serialize'
import type { DiagramWithBoundary } from '../diagram/boundary'
import { mkDiagramWithBoundary } from '../diagram/boundary'
import type { Definitions } from '../rules/definitions'
import { assertWellFormedDefinitions } from '../rules/definitions'
import type { ProofContext } from './step'
import type { Theorem } from './theorem'
import { checkTheorem } from './theorem'
import { dwbToJson, dwbFromJson, theoremToJson, theoremFromJson } from './json'
import { ProofError } from './error'

/**
 * A theory: definitions, named relations (comprehensions), and theorems in
 * registration order — later theorems may cite earlier ones by name. Semantic
 * content only (layer separation: no layout, no physics, ever).
 */
export type Theory = {
  readonly definitions: Definitions
  readonly relations: Readonly<Record<string, DiagramWithBoundary>>
  readonly theorems: readonly Theorem[]
}

/** Verify everything; returns the full proof context. There is no trust-without-verify path. */
export function verifyTheory(t: Theory): ProofContext {
  assertWellFormedDefinitions(t.definitions)
  for (const [name, rel] of Object.entries(t.relations)) {
    try {
      mkDiagramWithBoundary(rel.diagram, rel.boundary) // re-validates boundary existence/uniqueness
    } catch (e) {
      throw new ProofError(`relation '${name}': ${e instanceof Error ? e.message : String(e)}`)
    }
  }
  const theorems = new Map<string, Theorem>()
  for (const thm of t.theorems) {
    if (theorems.has(thm.name)) throw new ProofError(`duplicate theorem name '${thm.name}'`)
    checkTheorem(thm, { definitions: t.definitions, theorems })
    theorems.set(thm.name, thm)
  }
  return { definitions: t.definitions, theorems }
}

const FORMAT = 'visual-proof-theory'
const VERSION = 1

export function theoryToJson(t: Theory): unknown {
  const definitions: Record<string, string> = {}
  for (const [id, body] of Object.entries(t.definitions)) definitions[id] = serializeTerm(body)
  const relations: Record<string, unknown> = {}
  for (const [name, rel] of Object.entries(t.relations)) relations[name] = dwbToJson(rel)
  return {
    format: FORMAT,
    version: VERSION,
    definitions,
    relations,
    theorems: t.theorems.map(theoremToJson),
  }
}

function fail(msg: string): never {
  throw new Error(`malformed theory JSON: ${msg}`)
}

function isRecord(v: unknown): v is Record<string, unknown> {
  return typeof v === 'object' && v !== null && !Array.isArray(v)
}

export function theoryFromJson(j: unknown): Theory {
  if (!isRecord(j)) fail('top level must be an object')
  for (const k of Object.keys(j)) {
    if (!['format', 'version', 'definitions', 'relations', 'theorems'].includes(k)) {
      fail(`top level has unknown field '${k}' (semantic files carry no extra data)`)
    }
  }
  if (j.format !== FORMAT) fail(`unrecognized format '${String(j.format)}'`)
  if (j.version !== VERSION) fail(`unsupported version '${String(j.version)}' (expected ${VERSION})`)
  if (!isRecord(j.definitions) || !isRecord(j.relations) || !Array.isArray(j.theorems)) {
    fail("'definitions'/'relations' must be objects and 'theorems' an array")
  }
  const definitions: Record<string, Term> = {}
  for (const [id, v] of Object.entries(j.definitions)) {
    if (typeof v !== 'string') fail(`definition '${id}' must be a serialized term string`)
    try {
      definitions[id] = deserializeTerm(v)
    } catch (e) {
      fail(`definition '${id}': ${e instanceof Error ? e.message : String(e)}`)
    }
  }
  const relations: Record<string, DiagramWithBoundary> = {}
  for (const [name, v] of Object.entries(j.relations)) {
    relations[name] = dwbFromJson(v, `relation '${name}'`)
  }
  return { definitions, relations, theorems: j.theorems.map((t) => theoremFromJson(t)) }
}

/** Parse + verify: the only way to bring a theory file into the kernel. */
export function loadTheory(j: unknown): { theory: Theory; ctx: ProofContext } {
  const theory = theoryFromJson(j)
  return { theory, ctx: verifyTheory(theory) }
}
```

- [ ] **Step 4: Verify PASS, full suite, typecheck**

- [ ] **Step 5: Commit**

```bash
git add src/kernel/proof/store.ts tests/kernel/proof/store.test.ts
git commit -m "feat(kernel): verified theory store with versioned JSON format"
```

---

### Task 6: Proof barrel + end-to-end battery

**Files:**
- Create: `src/kernel/proof/index.ts`
- Test: `tests/kernel/proof/endtoend.test.ts`

- [ ] **Step 1: Write the battery** (must pass against Tasks 1–5; failures are bugs to fix test-first)

`tests/kernel/proof/endtoend.test.ts`:

```ts
import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../../src/kernel/term/parse'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { mkDiagramWithBoundary } from '../../../src/kernel/diagram/boundary'
import { mkSelection } from '../../../src/kernel/diagram/subgraph/selection'
import { diagramFingerprint } from '../../../src/kernel/diagram/canonical/fingerprint'
import {
  replayProof, composeProofs, checkTheorem, verifyTheory, loadTheory, theoryToJson,
} from '../../../src/kernel/proof/index'
import type { ProofStep, Theorem, Theory } from '../../../src/kernel/proof/index'

const noConsts = new Set<string>()
const p = (s: string) => parseTerm(s, noConsts)

describe('end to end: a sentence theorem built bidirectionally', () => {
  it('blank ⟹ ¬¬(empty cut pair) via forward and backward halves meeting in the middle', () => {
    // statement: from the empty sheet, derive a bare double cut.
    const blank = new DiagramBuilder().build()
    const goalBuilder = new DiagramBuilder()
    const outer = goalBuilder.cut(goalBuilder.root)
    goalBuilder.cut(outer)
    const goal = goalBuilder.build()

    // forward half: nothing (stay at blank). backward half, recorded against
    // an INDEPENDENTLY built blank (different from the forward side's blank
    // only in construction history — ids are deterministic, so exercise the
    // composition machinery anyway):
    const backwardStart = new DiagramBuilder().build()
    const tail: ProofStep[] = [{
      rule: 'doubleCutIntro',
      sel: mkSelection(backwardStart, { region: backwardStart.root, regions: [], nodes: [], wires: [] }),
    }]
    const composed = composeProofs(blank, backwardStart, tail, { definitions: {}, theorems: new Map() })
    const thm: Theorem = {
      name: 'blankToDoubleCut',
      lhs: mkDiagramWithBoundary(blank, []),
      rhs: mkDiagramWithBoundary(goal, []),
      steps: composed,
    }
    expect(() => checkTheorem(thm, { definitions: {}, theorems: new Map() })).not.toThrow()
  })
})

describe('end to end: derived rule proved, stored, loaded, applied natively', () => {
  function dropQ(): Theorem {
    const l = new DiagramBuilder()
    const lp = l.termNode(l.root, p('\\a. a'))
    const lq = l.termNode(l.root, p('\\a. \\b. a'))
    const lb = l.wire(l.root, [
      { node: lp, port: { kind: 'output' } },
      { node: lq, port: { kind: 'output' } },
    ])
    const lhs = mkDiagramWithBoundary(l.build(), [lb])
    const r = new DiagramBuilder()
    const rp = r.termNode(r.root, p('\\a. a'))
    const rb = r.wire(r.root, [{ node: rp, port: { kind: 'output' } }])
    const rhs = mkDiagramWithBoundary(r.build(), [rb])
    return {
      name: 'dropQ', lhs, rhs,
      steps: [{ rule: 'erasure', sel: { region: lhs.diagram.root, regions: [], nodes: [lq], wires: [] } }],
    }
  }

  it('save → load → apply in a host through a proof step', () => {
    const theory: Theory = { definitions: {}, relations: {}, theorems: [dropQ()] }
    const { ctx } = loadTheory(JSON.parse(JSON.stringify(theoryToJson(theory))))

    const h = new DiagramBuilder()
    const hp = h.termNode(h.root, p('\\a. a'))
    const hq = h.termNode(h.root, p('\\a. \\b. a'))
    const hub = h.termNode(h.root, p('y'))
    const v = h.wire(h.root, [
      { node: hp, port: { kind: 'output' } },
      { node: hq, port: { kind: 'output' } },
      { node: hub, port: { kind: 'freeVar', name: 'y' } },
    ])
    const d = h.build()
    const out = replayProof(d, [{
      rule: 'theorem', name: 'dropQ',
      at: { sel: { region: d.root, regions: [], nodes: [hp, hq], wires: [] }, args: [v] },
      direction: 'forward',
    }], ctx)
    // one application, regardless of the stored proof's length: hub + one P node
    expect(Object.values(out.nodes)).toHaveLength(2)
    expect(out.wires[v]?.endpoints).toHaveLength(2)
  })

  it('the whole pipeline preserves verification: tampered files are refused', () => {
    const theory: Theory = { definitions: {}, relations: {}, theorems: [dropQ()] }
    const j = JSON.parse(JSON.stringify(theoryToJson(theory))) as { theorems: { steps: unknown[] }[] }
    j.theorems[0]!.steps = [] // tamper: claim the theorem with no proof
    expect(() => loadTheory(j)).toThrowError(/does not arrive at the stated right-hand side/)
  })

  it('verifyTheory + fingerprints: applying a theorem equals replaying its expansion', () => {
    const t = dropQ()
    const ctx = verifyTheory({ definitions: {}, relations: {}, theorems: [t] })
    const h = new DiagramBuilder()
    const hp = h.termNode(h.root, p('\\a. a'))
    const hq = h.termNode(h.root, p('\\a. \\b. a'))
    const v = h.wire(h.root, [
      { node: hp, port: { kind: 'output' } },
      { node: hq, port: { kind: 'output' } },
    ])
    const d = h.build()
    const native = replayProof(d, [{
      rule: 'theorem', name: 'dropQ',
      at: { sel: { region: d.root, regions: [], nodes: [hp, hq], wires: [] }, args: [v] },
      direction: 'forward',
    }], ctx)
    // the same logical move done primitively: erase hq
    const primitive = replayProof(d, [{
      rule: 'erasure', sel: { region: d.root, regions: [], nodes: [hq], wires: [] },
    }], ctx)
    expect(diagramFingerprint(native)).toBe(diagramFingerprint(primitive))
  })
})
```

- [ ] **Step 2: Run; all must pass.** Any failure: investigate, fix test-first, report prominently.

- [ ] **Step 3: Write the barrel** `src/kernel/proof/index.ts`:

```ts
export { ProofError } from './error'
export type { ProofContext, ProofStep } from './step'
export { applyStep, replayProof } from './step'
export type { Theorem, TheoremApplication } from './theorem'
export { checkTheorem, applyTheorem } from './theorem'
export { composeProofs, mapStepIds } from './compose'
export {
  stepToJson, stepFromJson, theoremToJson, theoremFromJson, dwbToJson, dwbFromJson,
} from './json'
export type { Theory } from './store'
export { verifyTheory, theoryToJson, theoryFromJson, loadTheory } from './store'
```

- [ ] **Step 4: Full gate** — `npx vitest run && npx tsc --noEmit`; verify every export resolves.

- [ ] **Step 5: Commit**

```bash
git add src/kernel/proof/index.ts tests/kernel/proof/endtoend.test.ts
git commit -m "test(kernel): proof layer end-to-end battery; proof surface"
```

---

## Completion criteria for this plan

- `npx vitest run` green, `npx tsc --noEmit` clean.
- Demonstrated in tests: canonical labeling exposes discrete ordinals matching `canonicalForm` (full suite as the no-regression gate); `isoBetween` transports structure and handles automorphic diagrams; every step kind replays identically to its direct applier with gate refusals surfacing as `ProofError` naming the step; theorems verified by replay with boundary preservation and pinned-fingerprint conclusion checks; `applyTheorem` rewrites occurrences in ONE step (never expanding the stored proof), polarity-gated both directions, refusing mismatched occurrences by name; meet-in-the-middle composition rewrites multi-step tails (including steps referencing ids created mid-tail) across automorphic meets; all 16 step kinds round-trip through strict JSON; theory files re-verify on load, refuse tampering, and let later theorems use earlier ones (order-sensitive).
- Plan 9/10 build on `src/kernel/proof/index.ts` exports only.

## Carried obligations (forward)

- Plan 10 (session layer): interactive occurrence FINDING via the matcher feeds `TheoremApplication`s; bidirectional session = forward chain + backward tail + `composeProofs` at the meet.
- The abstraction R(x,x) limitation and the matcher bare-wire/symmetry items (Plans 6–7) remain.
- Plan 9 (or earlier if a second package appears): mechanical forbidden-import check (spec §4.2).
