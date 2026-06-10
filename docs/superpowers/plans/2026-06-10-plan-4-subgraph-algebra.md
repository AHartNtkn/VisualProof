# Subgraph Algebra Implementation Plan (Plan 4 of 8)

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** The subgraph operations every rule application stands on: βη-modulo node match keys, validated subgraph selection with wire classification, extraction to `DiagramWithBoundary` + attachment record, removal, and splice — with the round-trip law `splice(remove(h, sel), sel.region, extract(h, sel)) ≅ h` verified by fingerprint equality.

**Architecture:** Spec §3.7 (matching modulo βη: bounded normalize-and-compare, loud fuel exhaustion), §4.3 (kernel requirements). New directory `src/kernel/diagram/subgraph/` plus `src/kernel/diagram/canonical/matchkey.ts`. Pure, deterministic, every result re-validated through `mkDiagram`.

**Resolved carried obligation (from boundary.ts):** a pattern's boundary wires MUST be scoped at the pattern root; `spliceSubgraph` rejects anything else loudly. Rationale: a boundary wire is the connection seam to the enclosing context — its quantifier location after splicing IS the host attachment wire's scope, so a non-root scope inside the pattern would assert a quantifier location the splice cannot honor. `extractSubgraph` produces root-scoped boundary stubs by construction, so the law holds end-to-end.

**Key semantic decision — node match keys by closure:** two term nodes denote the same positional relation iff `λp0…λp(n-1). T` and `λp0…λp(n-1). T'` (terms closed over their free ports in first-occurrence order) are βη-convertible closed terms. Closing FIRST fixes the arity, so β-steps that would drop a free variable cannot desynchronize ports from wiring. Convertibility is decided by bounded normalization; exhaustion yields a loud `undecided` verdict, never a silent answer (undecidable in general — spec §3.7's honesty requirement).

**Plan sequence (matching moved into the rules plan, which consumes it):**

1. ✅ Kernel term layer. 2. ✅ Diagram syntax. 3. ✅ Canonicalization + fingerprints.
4. **This plan** — subgraph algebra (match keys, selection, extract, remove, splice).
5. Occurrence matcher (complete backtracking, anchored) + the eight foundational rule families, polarity-gated.
6. Derived rules, proof objects, bidirectional construction + replay, theory store + file format.
7. Deterministic layout + physics + rendering (Tromp bending, visual language).
8. App shell, interaction modes, persistence UI, bundled examples, end-to-end tests.

**House rules in force:** catch blocks use `e instanceof Error ? e.message : String(e)`; no silent failures; no heuristics; tests are the spec; fixes test-first.

---

### Task 1: Node match keys (closure + βη-modulo comparison)

**Files:**
- Create: `src/kernel/diagram/canonical/matchkey.ts`
- Test: `tests/kernel/diagram/matchkey.test.ts`

- [ ] **Step 1: Write the failing tests**

`tests/kernel/diagram/matchkey.test.ts`:

```ts
import { describe, it, expect } from 'vitest'
import { termEq, lam, bvar, app } from '../../../src/kernel/term/term'
import { parseTerm } from '../../../src/kernel/term/parse'
import { closeOverPorts, termsMatchModuloBetaEta } from '../../../src/kernel/diagram/canonical/matchkey'

const noConsts = new Set<string>()
const p = (s: string) => parseTerm(s, noConsts)

describe('closeOverPorts', () => {
  it('closes free ports as outermost lambdas in first-occurrence order', () => {
    // y z  →  \p0. \p1. p0 p1
    expect(termEq(closeOverPorts(p('y z')), p('\\a. \\b. a b'))).toBe(true)
    // y (z y)  →  \p0. \p1. p0 (p1 p0)
    expect(termEq(closeOverPorts(p('y (z y)')), p('\\a. \\b. a (b a)'))).toBe(true)
  })

  it('respects existing binders (ports skip over internal lambdas)', () => {
    // \x. y x  →  \p0. \x. p0 x
    expect(termEq(closeOverPorts(p('\\x. y x')), p('\\a. \\x. a x'))).toBe(true)
  })

  it('is the identity on closed terms', () => {
    const t = p('\\f. \\x. f (f x)')
    expect(termEq(closeOverPorts(t), t)).toBe(true)
  })

  it('rejects malformed terms loudly', () => {
    expect(() => closeOverPorts({ kind: 'bvar', index: 0 })).toThrowError(/unbound de Bruijn index/)
  })
})

describe('termsMatchModuloBetaEta', () => {
  it('matches free-variable renamings and beta-reducible forms', () => {
    expect(termsMatchModuloBetaEta(p('y z'), p('a b'), 100).status).toBe('match')
    expect(termsMatchModuloBetaEta(p('(\\x. x) (y z)'), p('y z'), 100).status).toBe('match')
  })

  it('matches eta-equal nodes of equal arity', () => {
    // node \x. f x (one port f) vs node f (one port f)
    expect(termsMatchModuloBetaEta(p('\\x. f x'), p('f'), 100).status).toBe('match')
  })

  it('rejects different arities without normalizing', () => {
    expect(termsMatchModuloBetaEta(p('y y'), p('y z'), 100).status).toBe('no-match')
  })

  it('rejects different positional relations of equal arity', () => {
    // \p0.\p1. p0 p1  vs  \p0.\p1. p0 (p0 p1) are not beta-eta-convertible
    expect(termsMatchModuloBetaEta(p('y z'), p('y (y z)'), 100).status).toBe('no-match')
  })

  it('treats naming positionally: y z and z y are the SAME relation', () => {
    // first-occurrence order puts the fn-position port at p0 in both terms;
    // names never carry content (consistent with termShapeKey)
    expect(termsMatchModuloBetaEta(p('y z'), p('z y'), 100).status).toBe('match')
  })

  it('matches identical non-normalizing terms by reflexivity (no spurious undecided)', () => {
    const omega = p('(\\x. x x) (\\x. x x)')
    expect(termsMatchModuloBetaEta(omega, omega, 25).status).toBe('match')
  })

  it('distinguishes and matches constant-carrying terms', () => {
    const pc = (s: string) => parseTerm(s, new Set(['plus', 'times']))
    expect(termsMatchModuloBetaEta(pc('plus y'), pc('times y'), 100).status).toBe('no-match')
    expect(termsMatchModuloBetaEta(pc('plus y'), pc('plus z'), 100).status).toBe('match')
  })

  it('rejects non-positive fuel as a caller error', () => {
    expect(() => termsMatchModuloBetaEta(p('y'), p('z'), 0)).toThrowError(/fuel must be a positive integer/i)
  })

  it('reports undecided on fuel exhaustion, naming the side', () => {
    const omega = p('(\\x. x x) (\\x. x x)')
    const left = termsMatchModuloBetaEta(omega, p('\\x. x'), 25)
    expect(left.status).toBe('undecided')
    if (left.status === 'undecided') expect(left.detail).toMatch(/left/i)
    const right = termsMatchModuloBetaEta(p('\\x. x'), omega, 25)
    expect(right.status).toBe('undecided')
    if (right.status === 'undecided') expect(right.detail).toMatch(/right/i)
  })
})
```

- [ ] **Step 2: Run tests to verify they fail**

Run: `npx vitest run tests/kernel/diagram/matchkey.test.ts`
Expected: FAIL — cannot resolve `canonical/matchkey`.

- [ ] **Step 3: Implement**

`src/kernel/diagram/canonical/matchkey.ts`:

```ts
import type { Term } from '../../term/term'
import { app, assertWellFormedTerm, bvar, cnst, freePorts, lam, termEq } from '../../term/term'
import { normalize } from '../../term/reduce'

/**
 * Close a term over its free ports in first-occurrence order: port i becomes
 * the i-th outermost lambda. Two nodes denote the same positional relation iff
 * their closures are beta-eta-convertible closed terms. Closing FIRST fixes
 * the arity, so normalization cannot drop a port out from under the wiring.
 */
export function closeOverPorts(t: Term): Term {
  assertWellFormedTerm(t)
  const order = freePorts(t)
  const n = order.length
  const index = new Map(order.map((name, i) => [name, i]))
  const walk = (u: Term, depth: number): Term => {
    switch (u.kind) {
      case 'port': {
        // index.get cannot miss: freePorts collects every port name
        const i = index.get(u.name)!
        // innermost closure lambda is p(n-1) at distance `depth`; p(i) sits
        // (n-1-i) binders further out
        return bvar(depth + (n - 1 - i))
      }
      case 'bvar': return bvar(u.index)
      case 'const': return cnst(u.id)
      case 'lam': return lam(walk(u.body, depth + 1))
      case 'app': return app(walk(u.fn, depth), walk(u.arg, depth))
    }
  }
  let closed = walk(t, 0)
  for (let i = 0; i < n; i++) closed = lam(closed)
  return closed
}

export type NodeMatchVerdict =
  | { readonly status: 'match' }
  | { readonly status: 'no-match' }
  | { readonly status: 'undecided'; readonly detail: string }

/**
 * Do two term nodes denote the same positional relation, modulo beta-eta?
 * Decided by bounded normalization of the port closures. Fuel exhaustion is a
 * loud 'undecided' verdict naming the side — never a silent answer; the
 * relation is undecidable in general (spec §3.7).
 */
export function termsMatchModuloBetaEta(a: Term, b: Term, fuel: number): NodeMatchVerdict {
  if (!Number.isInteger(fuel) || fuel <= 0) {
    throw new Error(`fuel must be a positive integer, got ${fuel}`)
  }
  if (freePorts(a).length !== freePorts(b).length) return { status: 'no-match' }
  const ca = closeOverPorts(a)
  const cb = closeOverPorts(b)
  // Sound shortcut, not a heuristic: structural equality of closures implies
  // convertibility by reflexivity — and avoids spurious 'undecided' verdicts
  // on identical non-normalizing terms.
  if (termEq(ca, cb)) return { status: 'match' }
  const na = normalize(ca, fuel)
  if (na.status === 'fuel-exhausted') {
    return { status: 'undecided', detail: `left closure did not normalize within ${fuel} steps` }
  }
  const nb = normalize(cb, fuel)
  if (nb.status === 'fuel-exhausted') {
    return { status: 'undecided', detail: `right closure did not normalize within ${fuel} steps` }
  }
  return termEq(na.term, nb.term) ? { status: 'match' } : { status: 'no-match' }
}
```

- [ ] **Step 4: Verify PASS, full suite, typecheck**

Run: `npx vitest run tests/kernel/diagram/matchkey.test.ts && npm test && npm run typecheck`

- [ ] **Step 5: Commit**

```bash
git add src/kernel/diagram/canonical/matchkey.ts tests/kernel/diagram/matchkey.test.ts
git commit -m "feat(kernel): node match keys via port closure, beta-eta-modulo comparison"
```

---

### Task 2: Subgraph selection and wire classification

**Files:**
- Create: `src/kernel/diagram/subgraph/selection.ts`
- Test: `tests/kernel/diagram/selection.test.ts`

- [ ] **Step 1: Write the failing tests**

`tests/kernel/diagram/selection.test.ts`:

```ts
import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../../src/kernel/term/parse'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { mkSelection, selectionContents } from '../../../src/kernel/diagram/subgraph/selection'

const noConsts = new Set<string>()
const p = (s: string) => parseTerm(s, noConsts)

// host: sheet contains node nA('y x'), cut C containing node nB('\x. x'),
// wire wShared (scope root) joining nA.v:y with nB.out (crosses into the cut),
// nA.out and nA.v:x auto-wired; plus a bare wire wBare scoped inside C.
function host() {
  const b = new DiagramBuilder()
  const nA = b.termNode(b.root, p('y x'))
  const cut = b.cut(b.root)
  const nB = b.termNode(cut, p('\\x. x'))
  const wShared = b.wire(b.root, [
    { node: nA, port: { kind: 'freeVar', name: 'y' } },
    { node: nB, port: { kind: 'output' } },
  ])
  const wBare = b.wire(cut, [])
  return { d: b.build(), nA, cut, nB, wShared, wBare }
}

describe('mkSelection', () => {
  it('validates region, child subtrees, direct nodes, explicit top-level wires', () => {
    const h = host()
    const sel = mkSelection(h.d, { region: h.d.root, regions: [h.cut], nodes: [h.nA], wires: [] })
    expect(sel.region).toBe(h.d.root)
  })

  it('rejects regions that are not children of the selection region', () => {
    const h = host()
    expect(() => mkSelection(h.d, { region: h.cut, regions: [h.cut], nodes: [], wires: [] }))
      .toThrowError(/region 'r1' is not a child of selection region 'r1'/)
  })

  it('rejects nodes not directly in the selection region, duplicates, and unknown ids', () => {
    const h = host()
    expect(() => mkSelection(h.d, { region: h.d.root, regions: [], nodes: [h.nB], wires: [] }))
      .toThrowError(/node 'n1' is not directly in selection region/)
    expect(() => mkSelection(h.d, { region: h.d.root, regions: [h.cut, h.cut], nodes: [], wires: [] }))
      .toThrowError(/duplicate selected region 'r1'/)
    expect(() => mkSelection(h.d, { region: h.d.root, regions: [], nodes: ['ghost'], wires: [] }))
      .toThrowError(/unknown node 'ghost'/)
  })

  it('rejects explicit wires not scoped at the region or with unselected endpoints', () => {
    const h = host()
    // wShared has an endpoint on nB (inside the cut) — selecting it without the cut fails
    expect(() => mkSelection(h.d, { region: h.d.root, regions: [], nodes: [h.nA], wires: [h.wShared] }))
      .toThrowError(/wire 'w0' has endpoints outside the selection/)
    // wBare is scoped inside the cut, not at the selection region
    expect(() => mkSelection(h.d, { region: h.d.root, regions: [], nodes: [h.nA], wires: [h.wBare] }))
      .toThrowError(/wire 'w1' is not scoped at selection region/)
  })
})

describe('selectionContents', () => {
  it('classifies wires: scoped-inside-subtree internal, cross-boundary touching', () => {
    const h = host()
    // select ONLY the cut subtree: nB inside, wShared touches nB from outside
    const sel = mkSelection(h.d, { region: h.d.root, regions: [h.cut], nodes: [], wires: [] })
    const c = selectionContents(h.d, sel)
    expect([...c.allRegions]).toEqual([h.cut])
    expect([...c.allNodes]).toEqual([h.nB])
    expect(c.internalWires).toContain(h.wBare) // scoped inside the selected cut
    expect(c.touchingWires).toContain(h.wShared) // endpoint on nB, scope outside
  })

  it('explicitly selected top-level wires are internal; unselected all-inside wires are touching', () => {
    const h = host()
    const withWire = mkSelection(h.d, {
      region: h.d.root, regions: [h.cut], nodes: [h.nA], wires: [h.wShared],
    })
    expect(selectionContents(h.d, withWire).internalWires).toContain(h.wShared)

    const withoutWire = mkSelection(h.d, {
      region: h.d.root, regions: [h.cut], nodes: [h.nA], wires: [],
    })
    // all endpoints selected, but membership is the caller's choice
    expect(selectionContents(h.d, withoutWire).touchingWires).toContain(h.wShared)
  })

  it('wires with no contact are neither internal nor touching', () => {
    const h = host()
    const sel = mkSelection(h.d, { region: h.d.root, regions: [], nodes: [h.nA], wires: [] })
    const c = selectionContents(h.d, sel)
    expect(c.internalWires).not.toContain(h.wBare)
    expect(c.touchingWires).not.toContain(h.wBare)
  })
})
```

- [ ] **Step 2: Run tests to verify they fail**

Run: `npx vitest run tests/kernel/diagram/selection.test.ts`
Expected: FAIL — cannot resolve `subgraph/selection`.

- [ ] **Step 3: Implement**

`src/kernel/diagram/subgraph/selection.ts`:

```ts
import type { Diagram, NodeId, RegionId, WireId } from '../diagram'
import { DiagramError } from '../diagram'

/**
 * A subgraph at a region: whole child subtrees, direct nodes, and explicitly
 * chosen top-level wires. Top-level wire membership is the caller's choice —
 * a wire whose endpoints all happen to be selected is still a boundary wire
 * unless listed in `wires`.
 */
export type SubgraphSelection = {
  readonly region: RegionId
  readonly regions: readonly RegionId[]
  readonly nodes: readonly NodeId[]
  readonly wires: readonly WireId[]
}

export type SelectionContents = {
  /** Every region inside the selected subtrees (the subtree roots included). */
  readonly allRegions: ReadonlySet<RegionId>
  /** Every selected node: direct ones plus all nodes inside selected subtrees. */
  readonly allNodes: ReadonlySet<NodeId>
  /** Wires wholly owned by the selection, sorted by id. */
  readonly internalWires: readonly WireId[]
  /** Wires with at least one endpoint on a selected node that are not internal, sorted by id. */
  readonly touchingWires: readonly WireId[]
}

export function mkSelection(d: Diagram, sel: SubgraphSelection): SubgraphSelection {
  if (d.regions[sel.region] === undefined) throw new DiagramError(`unknown selection region '${sel.region}'`)
  const seenR = new Set<RegionId>()
  for (const r of sel.regions) {
    const reg = d.regions[r]
    if (reg === undefined) throw new DiagramError(`unknown region '${r}'`)
    if (reg.kind === 'sheet' || reg.parent !== sel.region) {
      throw new DiagramError(`region '${r}' is not a child of selection region '${sel.region}'`)
    }
    if (seenR.has(r)) throw new DiagramError(`duplicate selected region '${r}'`)
    seenR.add(r)
  }
  const seenN = new Set<NodeId>()
  for (const n of sel.nodes) {
    const node = d.nodes[n]
    if (node === undefined) throw new DiagramError(`unknown node '${n}'`)
    if (node.region !== sel.region) {
      throw new DiagramError(`node '${n}' is not directly in selection region '${sel.region}'`)
    }
    if (seenN.has(n)) throw new DiagramError(`duplicate selected node '${n}'`)
    seenN.add(n)
  }
  // wire validation needs allNodes; compute the closure first
  const contents = computeClosure(d, sel.region, seenR, seenN)
  const seenW = new Set<WireId>()
  for (const w of sel.wires) {
    const wire = d.wires[w]
    if (wire === undefined) throw new DiagramError(`unknown wire '${w}'`)
    if (wire.scope !== sel.region) {
      throw new DiagramError(`wire '${w}' is not scoped at selection region '${sel.region}'`)
    }
    if (!wire.endpoints.every((ep) => contents.allNodes.has(ep.node))) {
      throw new DiagramError(`wire '${w}' has endpoints outside the selection`)
    }
    if (seenW.has(w)) throw new DiagramError(`duplicate selected wire '${w}'`)
    seenW.add(w)
  }
  return Object.freeze({
    region: sel.region,
    regions: Object.freeze([...sel.regions]),
    nodes: Object.freeze([...sel.nodes]),
    wires: Object.freeze([...sel.wires]),
  })
}

function computeClosure(
  d: Diagram,
  region: RegionId,
  subtreeRoots: ReadonlySet<RegionId>,
  directNodes: ReadonlySet<NodeId>,
): { allRegions: Set<RegionId>; allNodes: Set<NodeId> } {
  const allRegions = new Set<RegionId>(subtreeRoots)
  // expand subtrees: a region is included iff some ancestor chain hits a root
  let grew = true
  while (grew) {
    grew = false
    for (const [id, r] of Object.entries(d.regions)) {
      if (allRegions.has(id) || r.kind === 'sheet') continue
      if (allRegions.has(r.parent)) {
        allRegions.add(id)
        grew = true
      }
    }
  }
  const allNodes = new Set<NodeId>(directNodes)
  for (const [id, n] of Object.entries(d.nodes)) {
    if (allRegions.has(n.region)) allNodes.add(id)
  }
  return { allRegions, allNodes }
}

export function selectionContents(d: Diagram, sel: SubgraphSelection): SelectionContents {
  const { allRegions, allNodes } = computeClosure(
    d, sel.region, new Set(sel.regions), new Set(sel.nodes),
  )
  const explicit = new Set(sel.wires)
  const internalWires: WireId[] = []
  const touchingWires: WireId[] = []
  for (const [id, w] of Object.entries(d.wires)) {
    if (allRegions.has(w.scope) || explicit.has(id)) {
      internalWires.push(id)
      continue
    }
    if (w.endpoints.some((ep) => allNodes.has(ep.node))) touchingWires.push(id)
  }
  internalWires.sort()
  touchingWires.sort()
  return Object.freeze({
    allRegions,
    allNodes,
    internalWires: Object.freeze(internalWires),
    touchingWires: Object.freeze(touchingWires),
  })
}
```

- [ ] **Step 4: Verify PASS, full suite, typecheck**

- [ ] **Step 5: Commit**

```bash
git add src/kernel/diagram/subgraph/selection.ts tests/kernel/diagram/selection.test.ts
git commit -m "feat(kernel): validated subgraph selection with wire classification"
```

---

### Task 3: Extraction

**Files:**
- Create: `src/kernel/diagram/subgraph/extract.ts`
- Test: `tests/kernel/diagram/extract.test.ts`

- [ ] **Step 1: Write the failing tests**

`tests/kernel/diagram/extract.test.ts`:

```ts
import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../../src/kernel/term/parse'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { mkSelection } from '../../../src/kernel/diagram/subgraph/selection'
import { extractSubgraph } from '../../../src/kernel/diagram/subgraph/extract'
import { boundaryArity } from '../../../src/kernel/diagram/boundary'

const noConsts = new Set<string>()
const p = (s: string) => parseTerm(s, noConsts)

function host() {
  const b = new DiagramBuilder()
  const nA = b.termNode(b.root, p('y x'))
  const cut = b.cut(b.root)
  const nB = b.termNode(cut, p('\\x. x'))
  const wShared = b.wire(b.root, [
    { node: nA, port: { kind: 'freeVar', name: 'y' } },
    { node: nB, port: { kind: 'output' } },
  ])
  const wBare = b.wire(cut, [])
  return { d: b.build(), nA, cut, nB, wShared, wBare }
}

describe('extractSubgraph', () => {
  it('produces a valid pattern with root-scoped boundary stubs and an attachment record', () => {
    const h = host()
    const sel = mkSelection(h.d, { region: h.d.root, regions: [h.cut], nodes: [], wires: [] })
    const { pattern, attachments } = extractSubgraph(h.d, sel)
    // boundary: exactly the touching wire (wShared), as a root-scoped stub
    expect(boundaryArity(pattern)).toBe(1)
    expect(attachments).toEqual([h.wShared])
    const stubId = pattern.boundary[0]!
    const stub = pattern.diagram.wires[stubId]!
    expect(stub.scope).toBe(pattern.diagram.root)
    // the stub keeps only the selected endpoint (nB's output)
    expect(stub.endpoints).toHaveLength(1)
    expect(stub.endpoints[0]?.node).toBe(h.nB)
    // internal content carried over: the cut, nB, and the bare wire inside
    expect(Object.keys(pattern.diagram.regions)).toHaveLength(2) // fresh root + cut
    expect(pattern.diagram.nodes[h.nB]).toBeDefined()
    expect(pattern.diagram.wires[h.wBare]).toBeDefined()
  })

  it('maps selection-region scopes to the pattern root', () => {
    const h = host()
    const sel = mkSelection(h.d, {
      region: h.d.root, regions: [h.cut], nodes: [h.nA], wires: [h.wShared],
    })
    const { pattern, attachments } = extractSubgraph(h.d, sel)
    // wShared is internal here: copied with scope at the fresh root
    expect(pattern.diagram.wires[h.wShared]?.scope).toBe(pattern.diagram.root)
    // nA's other ports (out, v:x) were auto-wired at root scope in the host:
    // those host wires touch only nA, so they become boundary stubs
    expect(boundaryArity(pattern)).toBe(2)
    expect(attachments).toHaveLength(2)
  })

  it('orders boundary stubs deterministically by host wire id', () => {
    const h = host()
    const sel = mkSelection(h.d, {
      region: h.d.root, regions: [h.cut], nodes: [h.nA], wires: [h.wShared],
    })
    const { attachments } = extractSubgraph(h.d, sel)
    expect([...attachments]).toEqual([...attachments].sort())
  })

  it('extracted pattern is a valid diagram (re-validated through mkDiagram)', () => {
    const h = host()
    const sel = mkSelection(h.d, { region: h.d.root, regions: [h.cut], nodes: [], wires: [] })
    // construction inside extractSubgraph runs mkDiagram; reaching here means it passed
    expect(() => extractSubgraph(h.d, sel)).not.toThrow()
  })
})
```

- [ ] **Step 2: Run tests to verify they fail**

Run: `npx vitest run tests/kernel/diagram/extract.test.ts`
Expected: FAIL — cannot resolve `subgraph/extract`.

- [ ] **Step 3: Implement**

`src/kernel/diagram/subgraph/extract.ts`:

```ts
import type { Diagram, DiagramNode, Region, RegionId, Wire, WireId } from '../diagram'
import { mkDiagram } from '../diagram'
import type { DiagramWithBoundary } from '../boundary'
import { mkDiagramWithBoundary } from '../boundary'
import type { SubgraphSelection } from './selection'
import { selectionContents } from './selection'

export type Extraction = {
  readonly pattern: DiagramWithBoundary
  /** Host wires the boundary stubs came from, index-aligned with pattern.boundary. */
  readonly attachments: readonly WireId[]
}

function freshId(taken: ReadonlySet<string>, base: string): string {
  if (!taken.has(base)) return base
  for (let k = 0; ; k++) {
    const candidate = `${base}_${k}`
    if (!taken.has(candidate)) return candidate
  }
}

/**
 * Non-destructive: copies the selection out as a self-contained pattern.
 * Selected items keep their host ids (the pattern is a fresh namespace);
 * the fresh root and boundary stub ids dodge collisions deterministically.
 * Boundary stubs are root-scoped by construction — the invariant splice
 * relies on. Touching wires become stubs in sorted host-wire-id order,
 * keeping only the selected endpoints; the original host wire ids form the
 * attachment record.
 */
export function extractSubgraph(d: Diagram, sel: SubgraphSelection): Extraction {
  const c = selectionContents(d, sel)
  const takenRegionIds = new Set<string>(c.allRegions)
  const root = freshId(takenRegionIds, 'root')

  const regions: Record<RegionId, Region> = { [root]: { kind: 'sheet' } }
  for (const id of c.allRegions) {
    const r = d.regions[id]!
    if (r.kind === 'sheet') continue // impossible: subtree roots are non-root children
    const parent = id === sel.region ? root : (sel.regions.includes(id) ? root : r.parent)
    regions[id] = r.kind === 'cut'
      ? { kind: 'cut', parent }
      : { kind: 'bubble', parent, arity: r.arity }
  }

  const nodes: Record<string, DiagramNode> = {}
  for (const id of c.allNodes) {
    const n = d.nodes[id]!
    const region = n.region === sel.region ? root : n.region
    nodes[id] = n.kind === 'term'
      ? { kind: 'term', region, term: n.term }
      : { kind: 'atom', region, binder: n.binder }
  }

  const wires: Record<WireId, Wire> = {}
  const takenWireIds = new Set<string>(c.internalWires)
  for (const id of c.internalWires) {
    const w = d.wires[id]!
    wires[id] = {
      scope: w.scope === sel.region ? root : w.scope,
      endpoints: w.endpoints,
    }
  }

  const boundary: WireId[] = []
  const attachments: WireId[] = []
  for (const hostWireId of c.touchingWires) {
    const w = d.wires[hostWireId]!
    const stubId = freshId(takenWireIds, `b${boundary.length}`)
    takenWireIds.add(stubId)
    wires[stubId] = {
      scope: root,
      endpoints: w.endpoints.filter((ep) => c.allNodes.has(ep.node)),
    }
    boundary.push(stubId)
    attachments.push(hostWireId)
  }

  const pattern = mkDiagramWithBoundary(mkDiagram({ root, regions, nodes, wires }), boundary)
  return Object.freeze({ pattern, attachments: Object.freeze(attachments) })
}
```

- [ ] **Step 4: Verify PASS, full suite, typecheck**

- [ ] **Step 5: Commit**

```bash
git add src/kernel/diagram/subgraph/extract.ts tests/kernel/diagram/extract.test.ts
git commit -m "feat(kernel): subgraph extraction to boundary patterns with attachment records"
```

---

### Task 4: Removal and splice

**Files:**
- Create: `src/kernel/diagram/subgraph/splice.ts`
- Test: `tests/kernel/diagram/splice.test.ts`

- [ ] **Step 1: Write the failing tests**

`tests/kernel/diagram/splice.test.ts`:

```ts
import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../../src/kernel/term/parse'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { mkDiagramWithBoundary } from '../../../src/kernel/diagram/boundary'
import { mkSelection } from '../../../src/kernel/diagram/subgraph/selection'
import { extractSubgraph } from '../../../src/kernel/diagram/subgraph/extract'
import { removeSubgraph, spliceSubgraph } from '../../../src/kernel/diagram/subgraph/splice'

const noConsts = new Set<string>()
const p = (s: string) => parseTerm(s, noConsts)

function host() {
  const b = new DiagramBuilder()
  const nA = b.termNode(b.root, p('y x'))
  const cut = b.cut(b.root)
  const nB = b.termNode(cut, p('\\x. x'))
  const wShared = b.wire(b.root, [
    { node: nA, port: { kind: 'freeVar', name: 'y' } },
    { node: nB, port: { kind: 'output' } },
  ])
  const wBare = b.wire(cut, [])
  return { d: b.build(), nA, cut, nB, wShared, wBare }
}

describe('removeSubgraph', () => {
  it('drops selected content and trims touching wires to their outside endpoints', () => {
    const h = host()
    const sel = mkSelection(h.d, { region: h.d.root, regions: [h.cut], nodes: [], wires: [] })
    const after = removeSubgraph(h.d, sel)
    expect(after.regions[h.cut]).toBeUndefined()
    expect(after.nodes[h.nB]).toBeUndefined()
    expect(after.wires[h.wBare]).toBeUndefined()
    // wShared survives with only nA's endpoint
    expect(after.wires[h.wShared]?.endpoints).toHaveLength(1)
    expect(after.wires[h.wShared]?.endpoints[0]?.node).toBe(h.nA)
  })
})

describe('spliceSubgraph', () => {
  it('extract → remove → splice round-trips structurally (endpoint restored)', () => {
    const h = host()
    const sel = mkSelection(h.d, { region: h.d.root, regions: [h.cut], nodes: [], wires: [] })
    const { pattern, attachments } = extractSubgraph(h.d, sel)
    const removed = removeSubgraph(h.d, sel)
    const restored = spliceSubgraph(removed, h.d.root, pattern, attachments)
    // the shared wire regained a second endpoint
    expect(restored.wires[h.wShared]?.endpoints).toHaveLength(2)
    // one cut exists again, holding one node and one bare wire
    const cuts = Object.entries(restored.regions).filter(([, r]) => r.kind === 'cut')
    expect(cuts).toHaveLength(1)
  })

  it('rejects boundary wires not scoped at the pattern root (the resolved obligation)', () => {
    const b = new DiagramBuilder()
    const cut = b.cut(b.root)
    const n = b.termNode(cut, p('\\x. x'))
    const w = b.wire(cut, [{ node: n, port: { kind: 'output' } }]) // scoped INSIDE the cut
    const pattern = mkDiagramWithBoundary(b.build(), [w])
    const hostB = new DiagramBuilder()
    const hn = hostB.termNode(hostB.root, p('\\x. x'))
    const hw = hostB.wire(hostB.root, [{ node: hn, port: { kind: 'output' } }])
    expect(() => spliceSubgraph(hostB.build(), 'r0', pattern, [hw]))
      .toThrowError(/boundary wire 'w0' is not scoped at the pattern root; not spliceable/)
  })

  it('rejects attachment arity mismatches and attachments that cannot reach the splice region', () => {
    const h = host()
    const sel = mkSelection(h.d, { region: h.d.root, regions: [h.cut], nodes: [], wires: [] })
    const { pattern } = extractSubgraph(h.d, sel)
    expect(() => spliceSubgraph(h.d, h.d.root, pattern, []))
      .toThrowError(/expected 1 attachments, got 0/)
    expect(() => spliceSubgraph(h.d, h.d.root, pattern, ['ghost']))
      .toThrowError(/attachment wire 'ghost' does not exist/)
    // a wire scoped inside the cut cannot serve a splice at the root
    expect(() => spliceSubgraph(h.d, h.d.root, pattern, [h.wBare]))
      .toThrowError(/attachment wire 'w1' \(scope 'r1'\) does not enclose splice region 'r0'/)
  })

  it('generates fresh ids on collision and re-validates the result', () => {
    const h = host()
    const sel = mkSelection(h.d, { region: h.d.root, regions: [h.cut], nodes: [], wires: [] })
    const { pattern, attachments } = extractSubgraph(h.d, sel)
    // splice into the ORIGINAL host (not removed): ids collide, fresh ones must be coined
    const doubled = spliceSubgraph(h.d, h.d.root, pattern, attachments)
    const cuts = Object.entries(doubled.regions).filter(([, r]) => r.kind === 'cut')
    expect(cuts).toHaveLength(2)
    // wShared now carries nA + two copies of nB-output
    expect(doubled.wires[h.wShared]?.endpoints).toHaveLength(3)
  })

  it('two boundary stubs may attach to the same host wire', () => {
    // pattern: node 'y x' with both free-var stubs; attach both to one host wire
    const pb = new DiagramBuilder()
    const pn = pb.termNode(pb.root, p('y x'))
    const sY = pb.wire(pb.root, [{ node: pn, port: { kind: 'freeVar', name: 'y' } }])
    const sX = pb.wire(pb.root, [{ node: pn, port: { kind: 'freeVar', name: 'x' } }])
    const pd = pb.build() // pn.out auto-wired internally
    const pattern = mkDiagramWithBoundary(pd, [sY, sX])
    const hb = new DiagramBuilder()
    const hn = hb.termNode(hb.root, p('\\x. x'))
    const hw = hb.wire(hb.root, [{ node: hn, port: { kind: 'output' } }])
    const out = spliceSubgraph(hb.build(), 'r0', pattern, [hw, hw])
    expect(out.wires[hw]?.endpoints).toHaveLength(3) // hn.out + spliced y + spliced x
  })
})
```

- [ ] **Step 2: Run tests to verify they fail**

Run: `npx vitest run tests/kernel/diagram/splice.test.ts`
Expected: FAIL — cannot resolve `subgraph/splice`.

- [ ] **Step 3: Implement**

`src/kernel/diagram/subgraph/splice.ts`:

```ts
import type { Diagram, DiagramNode, Endpoint, Region, RegionId, Wire, WireId } from '../diagram'
import { DiagramError, mkDiagram } from '../diagram'
import { isAncestorOrEqual } from '../regions'
import type { DiagramWithBoundary } from '../boundary'
import type { SubgraphSelection } from './selection'
import { selectionContents } from './selection'

/** Drop the selection's content; touching wires keep only their outside endpoints. */
export function removeSubgraph(d: Diagram, sel: SubgraphSelection): Diagram {
  const c = selectionContents(d, sel)
  const internal = new Set(c.internalWires)
  const regions: Record<RegionId, Region> = {}
  for (const [id, r] of Object.entries(d.regions)) {
    if (!c.allRegions.has(id)) regions[id] = r
  }
  const nodes: Record<string, DiagramNode> = {}
  for (const [id, n] of Object.entries(d.nodes)) {
    if (!c.allNodes.has(id)) nodes[id] = n
  }
  const wires: Record<WireId, Wire> = {}
  for (const [id, w] of Object.entries(d.wires)) {
    if (internal.has(id)) continue
    wires[id] = {
      scope: w.scope,
      endpoints: w.endpoints.filter((ep) => !c.allNodes.has(ep.node)),
    }
  }
  return mkDiagram({ root: d.root, regions, nodes, wires })
}

function freshId(taken: ReadonlySet<string>, base: string): string {
  if (!taken.has(base)) return base
  for (let k = 0; ; k++) {
    const candidate = `${base}_${k}`
    if (!taken.has(candidate)) return candidate
  }
}

/**
 * Insert a pattern into a host region, merging each boundary stub's endpoints
 * into the index-aligned host attachment wire. Boundary stubs MUST be scoped
 * at the pattern root (the connection seam's quantifier location after the
 * splice IS the attachment wire's scope — a non-root stub scope would assert
 * a location the splice cannot honor; see boundary.ts). Pattern content gets
 * fresh host ids deterministically; the result is re-validated by mkDiagram.
 */
export function spliceSubgraph(
  host: Diagram,
  atRegion: RegionId,
  pattern: DiagramWithBoundary,
  attachments: readonly WireId[],
): Diagram {
  if (host.regions[atRegion] === undefined) {
    throw new DiagramError(`splice region '${atRegion}' does not exist`)
  }
  if (attachments.length !== pattern.boundary.length) {
    throw new DiagramError(`expected ${pattern.boundary.length} attachments, got ${attachments.length}`)
  }
  const pd = pattern.diagram
  const boundarySet = new Set(pattern.boundary)
  for (const b of pattern.boundary) {
    if (pd.wires[b]!.scope !== pd.root) {
      throw new DiagramError(`boundary wire '${b}' is not scoped at the pattern root; not spliceable`)
    }
  }
  for (const a of attachments) {
    const w = host.wires[a]
    if (w === undefined) throw new DiagramError(`attachment wire '${a}' does not exist`)
    if (!isAncestorOrEqual(host, w.scope, atRegion)) {
      throw new DiagramError(`attachment wire '${a}' (scope '${w.scope}') does not enclose splice region '${atRegion}'`)
    }
  }

  // fresh-id maps for pattern regions (except root), nodes, internal wires
  const takenRegions = new Set(Object.keys(host.regions))
  const regionMap = new Map<RegionId, RegionId>([[pd.root, atRegion]])
  for (const id of Object.keys(pd.regions)) {
    if (id === pd.root) continue
    const fresh = freshId(takenRegions, id)
    takenRegions.add(fresh)
    regionMap.set(id, fresh)
  }
  const takenNodes = new Set(Object.keys(host.nodes))
  const nodeMap = new Map<string, string>()
  for (const id of Object.keys(pd.nodes)) {
    const fresh = freshId(takenNodes, id)
    takenNodes.add(fresh)
    nodeMap.set(id, fresh)
  }
  const takenWires = new Set(Object.keys(host.wires))
  const wireMap = new Map<WireId, WireId>()
  for (const id of Object.keys(pd.wires)) {
    if (boundarySet.has(id)) continue
    const fresh = freshId(takenWires, id)
    takenWires.add(fresh)
    wireMap.set(id, fresh)
  }

  const regions: Record<RegionId, Region> = { ...host.regions }
  for (const [id, r] of Object.entries(pd.regions)) {
    if (id === pd.root) continue
    const mapped = regionMap.get(id)!
    if (r.kind === 'sheet') continue // impossible: single sheet is the root
    regions[mapped] = r.kind === 'cut'
      ? { kind: 'cut', parent: regionMap.get(r.parent)! }
      : { kind: 'bubble', parent: regionMap.get(r.parent)!, arity: r.arity }
  }

  const nodes: Record<string, DiagramNode> = { ...host.nodes }
  for (const [id, n] of Object.entries(pd.nodes)) {
    const mapped = nodeMap.get(id)!
    nodes[mapped] = n.kind === 'term'
      ? { kind: 'term', region: regionMap.get(n.region)!, term: n.term }
      : { kind: 'atom', region: regionMap.get(n.region)!, binder: regionMap.get(n.binder)! }
  }

  const mapEndpoints = (eps: readonly Endpoint[]): Endpoint[] =>
    eps.map((ep) => ({ node: nodeMap.get(ep.node)!, port: ep.port }))

  const wires: Record<WireId, Wire> = { ...host.wires }
  for (const [id, w] of Object.entries(pd.wires)) {
    if (boundarySet.has(id)) continue
    wires[wireMap.get(id)!] = {
      scope: regionMap.get(w.scope)!,
      endpoints: mapEndpoints(w.endpoints),
    }
  }
  pattern.boundary.forEach((stubId, i) => {
    const hostWireId = attachments[i]!
    const stub = pd.wires[stubId]!
    const existing = wires[hostWireId]!
    wires[hostWireId] = {
      scope: existing.scope,
      endpoints: [...existing.endpoints, ...mapEndpoints(stub.endpoints)],
    }
  })

  return mkDiagram({ root: host.root, regions, nodes, wires })
}
```

- [ ] **Step 4: Verify PASS, full suite, typecheck**

- [ ] **Step 5: Commit**

```bash
git add src/kernel/diagram/subgraph/splice.ts tests/kernel/diagram/splice.test.ts
git commit -m "feat(kernel): subgraph removal and splice with root-scope boundary enforcement"
```

---

### Task 5: Round-trip law + public surface

**Files:**
- Test: `tests/kernel/diagram/roundtrip.test.ts`
- Modify: `src/kernel/diagram/index.ts`

- [ ] **Step 1: Write the round-trip tests** (must pass against Tasks 2–4; failures are algebra bugs to fix test-first and report)

`tests/kernel/diagram/roundtrip.test.ts`:

```ts
import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../../src/kernel/term/parse'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { diagramFingerprint } from '../../../src/kernel/diagram/canonical/fingerprint'
import { mkSelection, type SubgraphSelection } from '../../../src/kernel/diagram/subgraph/selection'
import { extractSubgraph } from '../../../src/kernel/diagram/subgraph/extract'
import { removeSubgraph, spliceSubgraph } from '../../../src/kernel/diagram/subgraph/splice'

const noConsts = new Set<string>()
const p = (s: string) => parseTerm(s, noConsts)

function roundTrip(d: ReturnType<DiagramBuilder['build']>, sel: SubgraphSelection): void {
  const validated = mkSelection(d, sel)
  const { pattern, attachments } = extractSubgraph(d, validated)
  const removed = removeSubgraph(d, validated)
  const restored = spliceSubgraph(removed, validated.region, pattern, attachments)
  expect(diagramFingerprint(restored)).toBe(diagramFingerprint(d))
}

describe('extract → remove → splice round-trip (fingerprint identity)', () => {
  it('holds for a cut subtree with a crossing wire', () => {
    const b = new DiagramBuilder()
    const nA = b.termNode(b.root, p('y x'))
    const cut = b.cut(b.root)
    const nB = b.termNode(cut, p('\\x. x'))
    b.wire(b.root, [
      { node: nA, port: { kind: 'freeVar', name: 'y' } },
      { node: nB, port: { kind: 'output' } },
    ])
    b.wire(cut, [])
    const d = b.build()
    roundTrip(d, { region: d.root, regions: [cut], nodes: [], wires: [] })
  })

  it('holds for a bubble with atoms and a shared argument wire', () => {
    const b = new DiagramBuilder()
    const bub = b.bubble(b.root, 2)
    const t = b.termNode(bub, p('\\x. x'))
    const a = b.atom(bub, bub)
    b.wire(bub, [
      { node: t, port: { kind: 'output' } },
      { node: a, port: { kind: 'arg', index: 0 } },
      { node: a, port: { kind: 'arg', index: 1 } },
    ])
    const d = b.build()
    roundTrip(d, { region: d.root, regions: [bub], nodes: [], wires: [] })
  })

  it('holds for a mixed selection: direct node + subtree + explicit top-level wire', () => {
    const b = new DiagramBuilder()
    const nA = b.termNode(b.root, p('y x'))
    const cut = b.cut(b.root)
    const nB = b.termNode(cut, p('\\x. y x'))
    const w = b.wire(b.root, [
      { node: nA, port: { kind: 'freeVar', name: 'y' } },
      { node: nB, port: { kind: 'freeVar', name: 'y' } },
    ])
    const d = b.build()
    roundTrip(d, { region: d.root, regions: [cut], nodes: [nA], wires: [w] })
  })

  it('holds for a selection inside a nested region (splice point below the root)', () => {
    const b = new DiagramBuilder()
    const outer = b.cut(b.root)
    const inner = b.cut(outer)
    b.termNode(inner, p('\\x. x'))
    const nMid = b.termNode(outer, p('\\x. \\y. x'))
    void nMid
    const d = b.build()
    roundTrip(d, { region: outer, regions: [inner], nodes: [], wires: [] })
  })

  it('holds for the empty selection (degenerate identity)', () => {
    const b = new DiagramBuilder()
    b.termNode(b.root, p('\\x. x'))
    const d = b.build()
    roundTrip(d, { region: d.root, regions: [], nodes: [], wires: [] })
  })
})
```

- [ ] **Step 2: Run; all must pass.** Any failure is an algebra bug: investigate, fix test-first, report prominently.

- [ ] **Step 3: Extend the barrel** — append to `src/kernel/diagram/index.ts`:

```ts
export type { NodeMatchVerdict } from './canonical/matchkey'
export { closeOverPorts, termsMatchModuloBetaEta } from './canonical/matchkey'
export type { SubgraphSelection, SelectionContents } from './subgraph/selection'
export { mkSelection, selectionContents } from './subgraph/selection'
export type { Extraction } from './subgraph/extract'
export { extractSubgraph } from './subgraph/extract'
export { removeSubgraph, spliceSubgraph } from './subgraph/splice'
```

- [ ] **Step 4: Full gate** — `npm test && npm run typecheck`; verify every barrel export exists.

- [ ] **Step 5: Commit**

```bash
git add tests/kernel/diagram/roundtrip.test.ts src/kernel/diagram/index.ts
git commit -m "test(kernel): extract-remove-splice round-trip law; subgraph public surface"
```

---

## Completion criteria for this plan

- `npm test` green, `npm run typecheck` clean.
- Demonstrated in tests: closure-based βη-modulo node matching with loud undecided verdicts; selection validation with every violation rejected by name; wire classification (internal by subtree scope or explicit choice, touching by contact); extraction with root-scoped stubs and deterministic attachment order; removal trimming touching wires; splice enforcing the root-scope boundary obligation, coining fresh ids under collision, and supporting repeated attachments; the round-trip law verified by fingerprint identity on five diagram shapes including nested splice points.
- Plan 5 (matcher + rules) is written against these real exports.

## Carried obligations (forward)

- Plan 5: the occurrence matcher must be complete (match found iff exists) with the `undecided` channel surfaced in results; polarity gating via `polarity()`; exact-content matching below the top level of a pattern.
- Plan 7 (or earlier if a second package appears): mechanical forbidden-import check (spec §4.2).
