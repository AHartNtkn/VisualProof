# Diagram Syntax Implementation Plan (Plan 2 of 7)

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** The abstract syntax of diagrams — region trees (sheet/cuts/second-order bubbles), term nodes, relation atoms, wires-as-hyperedges with scopes — with construction-time well-formedness, region helpers (polarity), an ergonomic builder, JSON round-trip, and diagrams-with-boundary.

**Architecture:** Spec: `docs/superpowers/specs/2026-06-09-visual-proof-assistant-design.md` §2.2 (diagram constituents), §2.3 (parity), §4.3 (kernel requirements). Pure TypeScript under `src/kernel/diagram/`, importing only from `src/kernel/term/` modules directly (never from rendering/physics — they don't exist yet and never will be imported here). Invariant established here and relied on by all later plans: **the endpoint sets of wires exactly partition the set of all node ports** — every required port of every node is attached to exactly one wire; a "dangling" port does not exist (a lone port is a singleton wire). Invalid diagrams are unrepresentable through `mkDiagram`, the single validating constructor.

**Tech Stack:** TypeScript (strict), Vitest. No new dependencies.

**Plan sequence (renumbered — canonicalization split out as its own plan):**

1. ✅ Kernel term layer (merged).
2. **This plan** — diagram syntax, well-formedness, builder, JSON, boundaries.
3. Canonicalization + fingerprints (individualization-refinement canonical labeling; exact, not hash-based).
4. Foundational primitives 1–8, polarity-gated, matching modulo βη.
5. Derived rules, proof objects, bidirectional construction + replay, theory store + file format.
6. Deterministic layout + physics simulation + rendering (Tromp bending, visual language).
7. App shell, interaction modes, persistence UI, bundled examples, end-to-end tests.

**House rules in force:** catch blocks use `e instanceof Error ? e.message : String(e)`; every threshold justified; no silent failures; tests are the spec.

---

### Task 1: Diagram types, portKey, requiredPorts, mkDiagram happy path

**Files:**
- Create: `src/kernel/diagram/diagram.ts`
- Test: `tests/kernel/diagram/diagram.test.ts`

- [ ] **Step 1: Write the failing tests**

`tests/kernel/diagram/diagram.test.ts`:

```ts
import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../../src/kernel/term/parse'
import {
  mkDiagram, portKey, requiredPorts, DiagramError,
  type Region, type DiagramNode, type Wire,
} from '../../../src/kernel/diagram/diagram'

const noConsts = new Set<string>()
const p = (s: string) => parseTerm(s, noConsts)

describe('portKey', () => {
  it('produces distinct keys for the three port kinds', () => {
    expect(portKey({ kind: 'output' })).toBe('out')
    expect(portKey({ kind: 'freeVar', name: 'y' })).toBe('v:y')
    expect(portKey({ kind: 'arg', index: 2 })).toBe('a:2')
  })
})

describe('requiredPorts', () => {
  it('gives output plus one freeVar port per distinct free variable, in first-occurrence order', () => {
    const regions: Record<string, Region> = { r0: { kind: 'sheet' } }
    const node: DiagramNode = { kind: 'term', region: 'r0', term: p('\\x. y (z y x)') }
    expect(requiredPorts({ regions }, node).map(portKey)).toEqual(['out', 'v:y', 'v:z'])
  })

  it('gives arg ports 0..arity-1 for atoms, read from the binder bubble', () => {
    const regions: Record<string, Region> = {
      r0: { kind: 'sheet' },
      r1: { kind: 'bubble', parent: 'r0', arity: 2 },
    }
    const node: DiagramNode = { kind: 'atom', region: 'r1', binder: 'r1' }
    expect(requiredPorts({ regions }, node).map(portKey)).toEqual(['a:0', 'a:1'])
  })
})

describe('mkDiagram (happy path)', () => {
  it('constructs a valid diagram: bubble with one atom, a term node feeding both args', () => {
    // sheet > bubble(arity 2) containing atom X(t, t) where t is the output of \x.x
    const regions: Record<string, Region> = {
      r0: { kind: 'sheet' },
      r1: { kind: 'bubble', parent: 'r0', arity: 2 },
    }
    const nodes: Record<string, DiagramNode> = {
      n0: { kind: 'term', region: 'r1', term: p('\\x. x') },
      n1: { kind: 'atom', region: 'r1', binder: 'r1' },
    }
    const wires: Record<string, Wire> = {
      w0: {
        scope: 'r1',
        endpoints: [
          { node: 'n0', port: { kind: 'output' } },
          { node: 'n1', port: { kind: 'arg', index: 0 } },
          { node: 'n1', port: { kind: 'arg', index: 1 } },
        ],
      },
    }
    const d = mkDiagram({ root: 'r0', regions, nodes, wires })
    expect(d.root).toBe('r0')
    expect(Object.keys(d.regions)).toHaveLength(2)
    expect(Object.isFrozen(d)).toBe(true)
    expect(Object.isFrozen(d.nodes)).toBe(true)
  })

  it('accepts wires with zero endpoints (bare existence) and zero-arity bubbles', () => {
    const d = mkDiagram({
      root: 'r0',
      regions: { r0: { kind: 'sheet' }, r1: { kind: 'bubble', parent: 'r0', arity: 0 } },
      wires: { w0: { scope: 'r1', endpoints: [] } },
    })
    expect(d.wires['w0']?.endpoints).toHaveLength(0)
  })

  it('accepts a wire scoped above its endpoints (line of identity reaching into a cut)', () => {
    const regions: Record<string, Region> = {
      r0: { kind: 'sheet' },
      r1: { kind: 'cut', parent: 'r0' },
    }
    const nodes: Record<string, DiagramNode> = {
      n0: { kind: 'term', region: 'r0', term: p('\\x. x') },
      n1: { kind: 'term', region: 'r1', term: p('\\x. x') },
    }
    const wires: Record<string, Wire> = {
      w0: {
        scope: 'r0',
        endpoints: [
          { node: 'n0', port: { kind: 'output' } },
          { node: 'n1', port: { kind: 'output' } },
        ],
      },
    }
    expect(() => mkDiagram({ root: 'r0', regions, nodes, wires })).not.toThrow()
  })
})

describe('DiagramError', () => {
  it('is a distinct error class', () => {
    expect(new DiagramError('x')).toBeInstanceOf(Error)
    expect(new DiagramError('x').name).toBe('DiagramError')
  })
})
```

- [ ] **Step 2: Run tests to verify they fail**

Run: `npx vitest run tests/kernel/diagram/diagram.test.ts`
Expected: FAIL — cannot resolve `../../../src/kernel/diagram/diagram`.

- [ ] **Step 3: Implement**

`src/kernel/diagram/diagram.ts`:

```ts
import type { Term } from '../term/term'
import { freePorts } from '../term/term'

export type RegionId = string
export type NodeId = string
export type WireId = string

export type Region =
  | { readonly kind: 'sheet' }
  | { readonly kind: 'cut'; readonly parent: RegionId }
  | { readonly kind: 'bubble'; readonly parent: RegionId; readonly arity: number }

export type DiagramNode =
  | { readonly kind: 'term'; readonly region: RegionId; readonly term: Term }
  | { readonly kind: 'atom'; readonly region: RegionId; readonly binder: RegionId }

export type Port =
  | { readonly kind: 'output' }
  | { readonly kind: 'freeVar'; readonly name: string }
  | { readonly kind: 'arg'; readonly index: number }

export type Endpoint = { readonly node: NodeId; readonly port: Port }

/** One wire = one line of identity = one existentially scoped individual. */
export type Wire = { readonly scope: RegionId; readonly endpoints: readonly Endpoint[] }

export type Diagram = {
  readonly root: RegionId
  readonly regions: Readonly<Record<RegionId, Region>>
  readonly nodes: Readonly<Record<NodeId, DiagramNode>>
  readonly wires: Readonly<Record<WireId, Wire>>
}

export class DiagramError extends Error {
  constructor(message: string) {
    super(message)
    this.name = 'DiagramError'
  }
}

export function portKey(p: Port): string {
  switch (p.kind) {
    case 'output': return 'out'
    case 'freeVar': return `v:${p.name}`
    case 'arg': return `a:${p.index}`
  }
}

/**
 * The exact port set a node must have attached: output plus one freeVar port
 * per distinct free variable (first-occurrence order) for term nodes; arg
 * 0..arity-1 for atoms, arity read from the binder bubble.
 */
export function requiredPorts(d: { regions: Readonly<Record<RegionId, Region>> }, node: DiagramNode): Port[] {
  if (node.kind === 'term') {
    return [
      { kind: 'output' },
      ...freePorts(node.term).map((name): Port => ({ kind: 'freeVar', name })),
    ]
  }
  const binder = d.regions[node.binder]
  if (binder === undefined || binder.kind !== 'bubble') {
    throw new DiagramError(`atom binder '${node.binder}' is not a bubble`)
  }
  return Array.from({ length: binder.arity }, (_, index): Port => ({ kind: 'arg', index }))
}

function ancestorOrEqualRaw(regions: Readonly<Record<RegionId, Region>>, anc: RegionId, desc: RegionId): boolean {
  let cur: RegionId = desc
  for (;;) {
    if (cur === anc) return true
    const r = regions[cur]
    if (r === undefined || r.kind === 'sheet') return false
    cur = r.parent
  }
}

/**
 * The single validating constructor. Checks, in order: root is the unique
 * sheet; the parent graph is a tree rooted there; bubble arities are sane;
 * node regions and atom binders are valid (binder a bubble enclosing the
 * atom); wire scopes enclose every endpoint; and the wire endpoint sets
 * exactly partition the set of all required ports. Throws DiagramError with
 * a specific message on the first violation found.
 */
export function mkDiagram(parts: {
  root: RegionId
  regions: Record<RegionId, Region>
  nodes?: Record<NodeId, DiagramNode>
  wires?: Record<WireId, Wire>
}): Diagram {
  const { root: rootId } = parts
  const regions = parts.regions
  const nodes = parts.nodes ?? {}
  const wires = parts.wires ?? {}
  const fail = (msg: string): never => { throw new DiagramError(msg) }

  const root = regions[rootId] ?? fail(`root region '${rootId}' does not exist`)
  if (root.kind !== 'sheet') fail(`root region '${rootId}' must be a sheet, got '${root.kind}'`)

  for (const [id, r] of Object.entries(regions)) {
    if (r.kind === 'sheet' && id !== rootId) {
      fail(`region '${id}' is a second sheet; only the root may be a sheet`)
    }
    if (r.kind === 'bubble' && (!Number.isSafeInteger(r.arity) || r.arity < 0)) {
      fail(`bubble '${id}' arity must be a non-negative safe integer, got ${r.arity}`)
    }
    if (r.kind !== 'sheet' && regions[r.parent] === undefined) {
      fail(`region '${id}' has missing parent '${r.parent}'`)
    }
  }

  for (const id of Object.keys(regions)) {
    const seen = new Set<RegionId>()
    let cur = id
    for (;;) {
      if (seen.has(cur)) fail(`region parent chain from '${id}' contains a cycle at '${cur}'`)
      seen.add(cur)
      const r = regions[cur]!
      if (r.kind === 'sheet') break
      cur = r.parent
    }
  }

  for (const [id, n] of Object.entries(nodes)) {
    if (regions[n.region] === undefined) fail(`node '${id}' is in missing region '${n.region}'`)
    if (n.kind === 'atom') {
      const binder = regions[n.binder]
      if (binder === undefined) fail(`atom '${id}' references missing binder '${n.binder}'`)
      if (binder.kind !== 'bubble') fail(`atom '${id}' binder '${n.binder}' must be a bubble, got '${binder.kind}'`)
      if (!ancestorOrEqualRaw(regions, n.binder, n.region)) {
        fail(`atom '${id}' must lie inside its binder bubble '${n.binder}'`)
      }
    }
  }

  const attached = new Map<string, WireId>()
  for (const [wid, w] of Object.entries(wires)) {
    if (regions[w.scope] === undefined) fail(`wire '${wid}' has missing scope region '${w.scope}'`)
    for (const ep of w.endpoints) {
      const n = nodes[ep.node] ?? fail(`wire '${wid}' endpoint references missing node '${ep.node}'`)
      const key = portKey(ep.port)
      const req = requiredPorts({ regions }, n)
      if (!req.some((q) => portKey(q) === key)) {
        fail(`wire '${wid}' endpoint references non-existent port '${key}' of node '${ep.node}'`)
      }
      const akey = `${ep.node} ${key}`
      const prev = attached.get(akey)
      if (prev !== undefined) {
        fail(`port '${key}' of node '${ep.node}' is attached to two wires ('${prev}' and '${wid}')`)
      }
      attached.set(akey, wid)
      if (!ancestorOrEqualRaw(regions, w.scope, n.region)) {
        fail(`wire '${wid}' scope '${w.scope}' does not enclose node '${ep.node}' (region '${n.region}')`)
      }
    }
  }

  for (const [id, n] of Object.entries(nodes)) {
    for (const q of requiredPorts({ regions }, n)) {
      if (!attached.has(`${id} ${portKey(q)}`)) {
        fail(`port '${portKey(q)}' of node '${id}' is not attached to any wire`)
      }
    }
  }

  return Object.freeze({
    root: rootId,
    regions: Object.freeze({ ...regions }),
    nodes: Object.freeze({ ...nodes }),
    wires: Object.freeze({ ...wires }),
  })
}
```

- [ ] **Step 4: Run tests to verify they pass**

Run: `npx vitest run tests/kernel/diagram/diagram.test.ts`, then `npm test` and `npm run typecheck` — all green.

- [ ] **Step 5: Commit**

```bash
git add src/kernel/diagram/diagram.ts tests/kernel/diagram/diagram.test.ts
git commit -m "feat(kernel): diagram abstract syntax with validating constructor"
```

---

### Task 2: Well-formedness rejection battery

**Files:**
- Test: `tests/kernel/diagram/wellformed.test.ts`

Every invariant gets a violation test asserting its specific error message. No implementation changes are expected — if any test fails, the validator has a hole; fix `mkDiagram` (and report which hole).

- [ ] **Step 1: Write the tests**

`tests/kernel/diagram/wellformed.test.ts`:

```ts
import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../../src/kernel/term/parse'
import { mkDiagram, DiagramError, type Region, type DiagramNode, type Wire } from '../../../src/kernel/diagram/diagram'

const noConsts = new Set<string>()
const p = (s: string) => parseTerm(s, noConsts)

const sheet: Record<string, Region> = { r0: { kind: 'sheet' } }

describe('mkDiagram rejections', () => {
  it('rejects a missing root', () => {
    expect(() => mkDiagram({ root: 'nope', regions: sheet }))
      .toThrowError(/root region 'nope' does not exist/)
  })

  it('rejects a non-sheet root', () => {
    expect(() => mkDiagram({
      root: 'r1',
      regions: { r0: { kind: 'sheet' }, r1: { kind: 'cut', parent: 'r0' } },
    })).toThrowError(/root region 'r1' must be a sheet/)
  })

  it('rejects a second sheet', () => {
    expect(() => mkDiagram({
      root: 'r0',
      regions: { r0: { kind: 'sheet' }, r1: { kind: 'sheet' } },
    })).toThrowError(/second sheet/)
  })

  it('rejects negative and fractional bubble arity', () => {
    expect(() => mkDiagram({
      root: 'r0',
      regions: { r0: { kind: 'sheet' }, r1: { kind: 'bubble', parent: 'r0', arity: -1 } },
    })).toThrowError(/arity must be a non-negative safe integer/)
    expect(() => mkDiagram({
      root: 'r0',
      regions: { r0: { kind: 'sheet' }, r1: { kind: 'bubble', parent: 'r0', arity: 1.5 } },
    })).toThrowError(/arity must be a non-negative safe integer/)
  })

  it('rejects a missing parent', () => {
    expect(() => mkDiagram({
      root: 'r0',
      regions: { r0: { kind: 'sheet' }, r1: { kind: 'cut', parent: 'ghost' } },
    })).toThrowError(/missing parent 'ghost'/)
  })

  it('rejects a parent cycle', () => {
    expect(() => mkDiagram({
      root: 'r0',
      regions: {
        r0: { kind: 'sheet' },
        r1: { kind: 'cut', parent: 'r2' },
        r2: { kind: 'cut', parent: 'r1' },
      },
    })).toThrowError(/cycle/)
  })

  it('rejects a node in a missing region', () => {
    expect(() => mkDiagram({
      root: 'r0', regions: sheet,
      nodes: { n0: { kind: 'term', region: 'ghost', term: p('\\x. x') } },
    })).toThrowError(/node 'n0' is in missing region 'ghost'/)
  })

  it('rejects an atom whose binder is missing, not a bubble, or not enclosing', () => {
    const base: Record<string, Region> = {
      r0: { kind: 'sheet' },
      r1: { kind: 'bubble', parent: 'r0', arity: 0 },
      r2: { kind: 'cut', parent: 'r0' },
    }
    expect(() => mkDiagram({
      root: 'r0', regions: base,
      nodes: { n0: { kind: 'atom', region: 'r1', binder: 'ghost' } },
    })).toThrowError(/missing binder 'ghost'/)
    expect(() => mkDiagram({
      root: 'r0', regions: base,
      nodes: { n0: { kind: 'atom', region: 'r2', binder: 'r2' } },
    })).toThrowError(/must be a bubble/)
    // binder exists and is a bubble, but the atom sits outside it
    expect(() => mkDiagram({
      root: 'r0', regions: base,
      nodes: { n0: { kind: 'atom', region: 'r2', binder: 'r1' } },
    })).toThrowError(/must lie inside its binder/)
  })

  const oneNode = (wires: Record<string, Wire>) => {
    const nodes: Record<string, DiagramNode> = { n0: { kind: 'term', region: 'r0', term: p('\\x. x') } }
    return mkDiagram({ root: 'r0', regions: sheet, nodes, wires })
  }

  it('rejects a wire with a missing scope', () => {
    expect(() => oneNode({ w0: { scope: 'ghost', endpoints: [{ node: 'n0', port: { kind: 'output' } }] } }))
      .toThrowError(/missing scope region 'ghost'/)
  })

  it('rejects an endpoint on a missing node', () => {
    expect(() => oneNode({ w0: { scope: 'r0', endpoints: [{ node: 'ghost', port: { kind: 'output' } }] } }))
      .toThrowError(/missing node 'ghost'/)
  })

  it('rejects an endpoint on a non-existent port', () => {
    expect(() => oneNode({
      w0: { scope: 'r0', endpoints: [{ node: 'n0', port: { kind: 'freeVar', name: 'zz' } }] },
    })).toThrowError(/non-existent port 'v:zz'/)
  })

  it('rejects a port attached to two wires', () => {
    expect(() => oneNode({
      w0: { scope: 'r0', endpoints: [{ node: 'n0', port: { kind: 'output' } }] },
      w1: { scope: 'r0', endpoints: [{ node: 'n0', port: { kind: 'output' } }] },
    })).toThrowError(/attached to two wires/)
  })

  it('rejects an unattached port (the partition invariant)', () => {
    expect(() => oneNode({})).toThrowError(/port 'out' of node 'n0' is not attached/)
  })

  it('rejects a wire whose scope does not enclose an endpoint', () => {
    // node inside the sheet, wire scoped inside a cut that does not contain the node
    expect(() => mkDiagram({
      root: 'r0',
      regions: { r0: { kind: 'sheet' }, r1: { kind: 'cut', parent: 'r0' } },
      nodes: { n0: { kind: 'term', region: 'r0', term: p('\\x. x') } },
      wires: { w0: { scope: 'r1', endpoints: [{ node: 'n0', port: { kind: 'output' } }] } },
    })).toThrowError(/does not enclose node 'n0'/)
  })

  it('all rejections are DiagramError instances', () => {
    try {
      mkDiagram({ root: 'nope', regions: sheet })
      expect.unreachable('should have thrown')
    } catch (e) {
      expect(e).toBeInstanceOf(DiagramError)
    }
  })
})
```

- [ ] **Step 2: Run the battery**

Run: `npx vitest run tests/kernel/diagram/wellformed.test.ts`
Expected: PASS if Task 1's validator is complete. Any failure = validator hole; fix `mkDiagram` and report which invariant had the hole.

- [ ] **Step 3: Run full suite and commit**

Run: `npm test && npm run typecheck` — all green.

```bash
git add tests/kernel/diagram/wellformed.test.ts src/kernel/diagram/diagram.ts
git commit -m "test(kernel): well-formedness rejection battery for diagrams"
```

---

### Task 3: Region helpers — ancestry, cut depth, polarity

**Files:**
- Create: `src/kernel/diagram/regions.ts`
- Test: `tests/kernel/diagram/regions.test.ts`

- [ ] **Step 1: Write the failing tests**

`tests/kernel/diagram/regions.test.ts`:

```ts
import { describe, it, expect } from 'vitest'
import { mkDiagram, type Region } from '../../../src/kernel/diagram/diagram'
import { isAncestorOrEqual, cutDepth, polarity } from '../../../src/kernel/diagram/regions'

// sheet > cut1 > bubble > cut2 ; sheet > bubble2
const regions: Record<string, Region> = {
  r0: { kind: 'sheet' },
  r1: { kind: 'cut', parent: 'r0' },
  r2: { kind: 'bubble', parent: 'r1', arity: 1 },
  r3: { kind: 'cut', parent: 'r2' },
  r4: { kind: 'bubble', parent: 'r0', arity: 0 },
}
const d = mkDiagram({ root: 'r0', regions })

describe('isAncestorOrEqual', () => {
  it('is reflexive and follows the parent chain', () => {
    expect(isAncestorOrEqual(d, 'r0', 'r0')).toBe(true)
    expect(isAncestorOrEqual(d, 'r0', 'r3')).toBe(true)
    expect(isAncestorOrEqual(d, 'r1', 'r3')).toBe(true)
    expect(isAncestorOrEqual(d, 'r3', 'r1')).toBe(false)
    expect(isAncestorOrEqual(d, 'r4', 'r3')).toBe(false)
  })

  it('throws on unknown region ids', () => {
    expect(() => isAncestorOrEqual(d, 'ghost', 'r0')).toThrowError(/unknown region 'ghost'/)
    expect(() => isAncestorOrEqual(d, 'r0', 'ghost')).toThrowError(/unknown region 'ghost'/)
  })
})

describe('cutDepth and polarity', () => {
  it('counts cuts on the path from root, inclusive; bubbles do not count', () => {
    expect(cutDepth(d, 'r0')).toBe(0)
    expect(cutDepth(d, 'r1')).toBe(1)
    expect(cutDepth(d, 'r2')).toBe(1) // bubble does not add
    expect(cutDepth(d, 'r3')).toBe(2)
    expect(cutDepth(d, 'r4')).toBe(0)
  })

  it('polarity is positive iff cut depth is even — bubbles never flip it', () => {
    expect(polarity(d, 'r0')).toBe('positive')
    expect(polarity(d, 'r1')).toBe('negative')
    expect(polarity(d, 'r2')).toBe('negative')
    expect(polarity(d, 'r3')).toBe('positive')
    expect(polarity(d, 'r4')).toBe('positive')
  })

  it('throws on unknown region ids', () => {
    expect(() => cutDepth(d, 'ghost')).toThrowError(/unknown region 'ghost'/)
    expect(() => polarity(d, 'ghost')).toThrowError(/unknown region 'ghost'/)
  })
})
```

- [ ] **Step 2: Run tests to verify they fail**

Run: `npx vitest run tests/kernel/diagram/regions.test.ts`
Expected: FAIL — cannot resolve `regions`.

- [ ] **Step 3: Implement**

`src/kernel/diagram/regions.ts`:

```ts
import type { Diagram, RegionId } from './diagram'
import { DiagramError } from './diagram'

function regionOf(d: Diagram, id: RegionId) {
  const r = d.regions[id]
  if (r === undefined) throw new DiagramError(`unknown region '${id}'`)
  return r
}

/** True iff anc lies on the parent chain of desc (inclusive). */
export function isAncestorOrEqual(d: Diagram, anc: RegionId, desc: RegionId): boolean {
  regionOf(d, anc)
  let cur = desc
  for (;;) {
    const r = regionOf(d, cur)
    if (cur === anc) return true
    if (r.kind === 'sheet') return false
    cur = r.parent
  }
}

/** Number of cuts on the path from the root to r, counting r itself if it is a cut. */
export function cutDepth(d: Diagram, id: RegionId): number {
  let depth = 0
  let cur = id
  for (;;) {
    const r = regionOf(d, cur)
    if (r.kind === 'cut') depth++
    if (r.kind === 'sheet') return depth
    cur = r.parent
  }
}

/**
 * Positive iff the cut depth is even. Bubbles are quantifiers, not negations:
 * they never affect parity (spec §2.1).
 */
export function polarity(d: Diagram, id: RegionId): 'positive' | 'negative' {
  return cutDepth(d, id) % 2 === 0 ? 'positive' : 'negative'
}
```

- [ ] **Step 4: Verify PASS, full suite, typecheck**

Run: `npx vitest run tests/kernel/diagram/regions.test.ts && npm test && npm run typecheck`

- [ ] **Step 5: Commit**

```bash
git add src/kernel/diagram/regions.ts tests/kernel/diagram/regions.test.ts
git commit -m "feat(kernel): region ancestry, cut depth, polarity helpers"
```

---

### Task 4: DiagramBuilder

**Files:**
- Create: `src/kernel/diagram/builder.ts`
- Test: `tests/kernel/diagram/builder.test.ts`

- [ ] **Step 1: Write the failing tests**

`tests/kernel/diagram/builder.test.ts`:

```ts
import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../../src/kernel/term/parse'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { portKey } from '../../../src/kernel/diagram/diagram'

const noConsts = new Set<string>()
const p = (s: string) => parseTerm(s, noConsts)

describe('DiagramBuilder', () => {
  it('builds a valid diagram with deterministic ids', () => {
    const b = new DiagramBuilder()
    const cut = b.cut(b.root)
    const bub = b.bubble(cut, 1)
    const t = b.termNode(bub, p('\\x. x'))
    const a = b.atom(bub, bub)
    b.wire(bub, [
      { node: t, port: { kind: 'output' } },
      { node: a, port: { kind: 'arg', index: 0 } },
    ])
    const d = b.build()
    expect(cut).toBe('r1')
    expect(bub).toBe('r2')
    expect(t).toBe('n0')
    expect(a).toBe('n1')
    expect(Object.keys(d.wires)).toEqual(['w0'])
    expect(d.regions['r2']).toEqual({ kind: 'bubble', parent: 'r1', arity: 1 })
  })

  it('auto-attaches a fresh singleton wire to every unattached port, scoped at the node region', () => {
    const b = new DiagramBuilder()
    const t = b.termNode(b.root, p('\\x. y (z x)')) // ports: out, v:y, v:z — none wired
    const d = b.build()
    const wires = Object.values(d.wires)
    expect(wires).toHaveLength(3)
    const keys = wires.flatMap((w) => w.endpoints.map((ep) => `${ep.node}/${portKey(ep.port)}`)).sort()
    expect(keys).toEqual([`${t}/out`, `${t}/v:y`, `${t}/v:z`])
    for (const w of wires) {
      expect(w.scope).toBe(b.root)
      expect(w.endpoints).toHaveLength(1)
    }
  })

  it('produces a diagram that passes validation even with mixed manual and auto wires', () => {
    const b = new DiagramBuilder()
    const t1 = b.termNode(b.root, p('\\x. y x'))
    const t2 = b.termNode(b.root, p('\\x. x'))
    b.wire(b.root, [
      { node: t1, port: { kind: 'freeVar', name: 'y' } },
      { node: t2, port: { kind: 'output' } },
    ])
    const d = b.build() // t1/out auto-wired
    expect(Object.keys(d.wires)).toHaveLength(2)
  })

  it('build() is repeatable and rejects double-building mutations cleanly', () => {
    const b = new DiagramBuilder()
    b.termNode(b.root, p('\\x. x'))
    const d1 = b.build()
    const d2 = b.build()
    expect(Object.keys(d1.wires)).toEqual(Object.keys(d2.wires))
  })
})
```

- [ ] **Step 2: Run tests to verify they fail**

Run: `npx vitest run tests/kernel/diagram/builder.test.ts`
Expected: FAIL — cannot resolve `builder`.

- [ ] **Step 3: Implement**

`src/kernel/diagram/builder.ts`:

```ts
import type { Term } from '../term/term'
import type { Diagram, Endpoint, NodeId, Region, RegionId, DiagramNode, Wire, WireId } from './diagram'
import { mkDiagram, portKey, requiredPorts } from './diagram'

/**
 * Ergonomic incremental construction with deterministic ids (r0, r1, …; n0, …;
 * w0, …; auto-wires continue the w-counter). On build(), every port not
 * attached by an explicit wire receives a fresh singleton wire scoped at its
 * node's own region — establishing the partition invariant mechanically.
 * build() validates via mkDiagram and does not mutate builder state, so it is
 * repeatable.
 */
export class DiagramBuilder {
  readonly root: RegionId = 'r0'
  private regionCount = 1
  private nodeCount = 0
  private wireCount = 0
  private readonly regions: Record<RegionId, Region> = { r0: { kind: 'sheet' } }
  private readonly nodes: Record<NodeId, DiagramNode> = {}
  private readonly wires: Record<WireId, Wire> = {}

  cut(parent: RegionId): RegionId {
    const id = `r${this.regionCount++}`
    this.regions[id] = { kind: 'cut', parent }
    return id
  }

  bubble(parent: RegionId, arity: number): RegionId {
    const id = `r${this.regionCount++}`
    this.regions[id] = { kind: 'bubble', parent, arity }
    return id
  }

  termNode(region: RegionId, term: Term): NodeId {
    const id = `n${this.nodeCount++}`
    this.nodes[id] = { kind: 'term', region, term }
    return id
  }

  atom(region: RegionId, binder: RegionId): NodeId {
    const id = `n${this.nodeCount++}`
    this.nodes[id] = { kind: 'atom', region, binder }
    return id
  }

  wire(scope: RegionId, endpoints: Endpoint[]): WireId {
    const id = `w${this.wireCount++}`
    this.wires[id] = { scope, endpoints }
    return id
  }

  build(): Diagram {
    const attached = new Set<string>()
    for (const w of Object.values(this.wires)) {
      for (const ep of w.endpoints) attached.add(`${ep.node} ${portKey(ep.port)}`)
    }
    const autoWires: Record<WireId, Wire> = {}
    let auto = this.wireCount
    for (const [id, n] of Object.entries(this.nodes)) {
      for (const q of requiredPorts({ regions: this.regions }, n)) {
        if (!attached.has(`${id} ${portKey(q)}`)) {
          autoWires[`w${auto++}`] = { scope: n.region, endpoints: [{ node: id, port: q }] }
        }
      }
    }
    return mkDiagram({
      root: this.root,
      regions: { ...this.regions },
      nodes: { ...this.nodes },
      wires: { ...this.wires, ...autoWires },
    })
  }
}
```

- [ ] **Step 4: Verify PASS, full suite, typecheck**

Run: `npx vitest run tests/kernel/diagram/builder.test.ts && npm test && npm run typecheck`

- [ ] **Step 5: Commit**

```bash
git add src/kernel/diagram/builder.ts tests/kernel/diagram/builder.test.ts
git commit -m "feat(kernel): DiagramBuilder with auto-singleton wires"
```

---

### Task 5: Diagram JSON round-trip

**Files:**
- Create: `src/kernel/diagram/json.ts`
- Test: `tests/kernel/diagram/json.test.ts`

- [ ] **Step 1: Write the failing tests**

`tests/kernel/diagram/json.test.ts`:

```ts
import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../../src/kernel/term/parse'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { diagramToJson, diagramFromJson } from '../../../src/kernel/diagram/json'

const noConsts = new Set<string>()
const p = (s: string) => parseTerm(s, noConsts)

function sample() {
  const b = new DiagramBuilder()
  const cut = b.cut(b.root)
  const bub = b.bubble(cut, 2)
  const t = b.termNode(bub, p('\\x. y x'))
  const a = b.atom(bub, bub)
  b.wire(bub, [
    { node: t, port: { kind: 'output' } },
    { node: a, port: { kind: 'arg', index: 0 } },
    { node: a, port: { kind: 'arg', index: 1 } },
  ])
  return b.build()
}

describe('diagram JSON', () => {
  it('round-trips structurally: toJson ∘ fromJson ∘ toJson is the identity on JSON', () => {
    const d = sample()
    const j1 = diagramToJson(d)
    const d2 = diagramFromJson(j1)
    const j2 = diagramToJson(d2)
    expect(JSON.stringify(j2)).toBe(JSON.stringify(j1))
  })

  it('serializes terms via the injective term serialization', () => {
    const d = sample()
    const j = diagramToJson(d) as { nodes: Record<string, { kind: string; term?: string }> }
    expect(j.nodes['n0']?.term).toBe('L(A(P("y"),#0))')
  })

  it('rejects malformed JSON loudly: bad shape, bad port key, bad term', () => {
    expect(() => diagramFromJson(null)).toThrowError(/malformed diagram/i)
    expect(() => diagramFromJson({ root: 'r0' })).toThrowError(/malformed diagram/i)
    const d = sample()
    const good = JSON.parse(JSON.stringify(diagramToJson(d))) as Record<string, unknown>
    const badPort = JSON.parse(JSON.stringify(good)) as { wires: Record<string, { endpoints: { port: string }[] }> }
    badPort.wires['w0']!.endpoints[0]!.port = 'zzz'
    expect(() => diagramFromJson(badPort)).toThrowError(/malformed diagram.*port key 'zzz'/i)
    const badTerm = JSON.parse(JSON.stringify(good)) as { nodes: Record<string, { term?: string }> }
    badTerm.nodes['n0']!.term = 'garbage'
    expect(() => diagramFromJson(badTerm)).toThrowError(/malformed/i)
  })

  it('re-validates: structurally well-shaped JSON encoding an invalid diagram is rejected', () => {
    const d = sample()
    const j = JSON.parse(JSON.stringify(diagramToJson(d))) as { nodes: Record<string, { region: string }> }
    j.nodes['n0']!.region = 'ghost'
    expect(() => diagramFromJson(j)).toThrowError(/missing region 'ghost'/)
  })
})
```

- [ ] **Step 2: Run tests to verify they fail**

Run: `npx vitest run tests/kernel/diagram/json.test.ts`
Expected: FAIL — cannot resolve `json`.

- [ ] **Step 3: Implement**

`src/kernel/diagram/json.ts`:

```ts
import { deserializeTerm, serializeTerm } from '../term/serialize'
import type { Diagram, Port, Region, DiagramNode, Wire } from './diagram'
import { mkDiagram, portKey } from './diagram'

/**
 * Pure-data JSON form of a diagram. Semantic content only — by the layer
 * separation edict there is nothing else to save. Terms are embedded as
 * injective term-serialization strings; ports as portKey strings. Ids are
 * preserved verbatim. Theory files (Plan 5) wrap this in their own versioned
 * envelope; this object carries no version of its own.
 */
export function diagramToJson(d: Diagram): unknown {
  const regions: Record<string, unknown> = {}
  for (const [id, r] of Object.entries(d.regions)) regions[id] = { ...r }
  const nodes: Record<string, unknown> = {}
  for (const [id, n] of Object.entries(d.nodes)) {
    nodes[id] = n.kind === 'term'
      ? { kind: 'term', region: n.region, term: serializeTerm(n.term) }
      : { kind: 'atom', region: n.region, binder: n.binder }
  }
  const wires: Record<string, unknown> = {}
  for (const [id, w] of Object.entries(d.wires)) {
    wires[id] = {
      scope: w.scope,
      endpoints: w.endpoints.map((ep) => ({ node: ep.node, port: portKey(ep.port) })),
    }
  }
  return { root: d.root, regions, nodes, wires }
}

function fail(msg: string): never {
  throw new Error(`malformed diagram JSON: ${msg}`)
}

function isRecord(v: unknown): v is Record<string, unknown> {
  return typeof v === 'object' && v !== null && !Array.isArray(v)
}

function parsePortKey(key: string): Port {
  if (key === 'out') return { kind: 'output' }
  if (key.startsWith('v:') && key.length > 2) return { kind: 'freeVar', name: key.slice(2) }
  if (key.startsWith('a:')) {
    const n = Number(key.slice(2))
    if (Number.isSafeInteger(n) && n >= 0) return { kind: 'arg', index: n }
  }
  return fail(`unrecognized port key '${key}'`)
}

export function diagramFromJson(j: unknown): Diagram {
  if (!isRecord(j)) fail('top level must be an object')
  const { root, regions: jr, nodes: jn, wires: jw } = j
  if (typeof root !== 'string') fail("'root' must be a string")
  if (!isRecord(jr) || !isRecord(jn ?? {}) || !isRecord(jw ?? {})) fail("'regions', 'nodes', 'wires' must be objects")

  const regions: Record<string, Region> = {}
  for (const [id, v] of Object.entries(jr)) {
    if (!isRecord(v)) fail(`region '${id}' must be an object`)
    if (v.kind === 'sheet') { regions[id] = { kind: 'sheet' }; continue }
    if (v.kind === 'cut' && typeof v.parent === 'string') { regions[id] = { kind: 'cut', parent: v.parent }; continue }
    if (v.kind === 'bubble' && typeof v.parent === 'string' && typeof v.arity === 'number') {
      regions[id] = { kind: 'bubble', parent: v.parent, arity: v.arity }
      continue
    }
    fail(`region '${id}' has unrecognized shape`)
  }

  const nodes: Record<string, DiagramNode> = {}
  for (const [id, v] of Object.entries((jn ?? {}) as Record<string, unknown>)) {
    if (!isRecord(v) || typeof v.region !== 'string') fail(`node '${id}' has unrecognized shape`)
    if (v.kind === 'term' && typeof v.term === 'string') {
      nodes[id] = { kind: 'term', region: v.region, term: deserializeTerm(v.term) }
      continue
    }
    if (v.kind === 'atom' && typeof v.binder === 'string') {
      nodes[id] = { kind: 'atom', region: v.region, binder: v.binder }
      continue
    }
    fail(`node '${id}' has unrecognized shape`)
  }

  const wires: Record<string, Wire> = {}
  for (const [id, v] of Object.entries((jw ?? {}) as Record<string, unknown>)) {
    if (!isRecord(v) || typeof v.scope !== 'string' || !Array.isArray(v.endpoints)) {
      fail(`wire '${id}' has unrecognized shape`)
    }
    const endpoints = v.endpoints.map((ep, k) => {
      if (!isRecord(ep) || typeof ep.node !== 'string' || typeof ep.port !== 'string') {
        return fail(`wire '${id}' endpoint ${k} has unrecognized shape`)
      }
      return { node: ep.node, port: parsePortKey(ep.port) }
    })
    wires[id] = { scope: v.scope, endpoints }
  }

  return mkDiagram({ root, regions, nodes, wires })
}
```

- [ ] **Step 4: Verify PASS, full suite, typecheck**

Run: `npx vitest run tests/kernel/diagram/json.test.ts && npm test && npm run typecheck`

- [ ] **Step 5: Commit**

```bash
git add src/kernel/diagram/json.ts tests/kernel/diagram/json.test.ts
git commit -m "feat(kernel): diagram JSON round-trip with loud rejection and re-validation"
```

---

### Task 6: Diagrams with boundary

**Files:**
- Create: `src/kernel/diagram/boundary.ts`
- Test: `tests/kernel/diagram/boundary.test.ts`

- [ ] **Step 1: Write the failing tests**

`tests/kernel/diagram/boundary.test.ts`:

```ts
import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../../src/kernel/term/parse'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { mkDiagramWithBoundary, boundaryArity } from '../../../src/kernel/diagram/boundary'

const noConsts = new Set<string>()
const p = (s: string) => parseTerm(s, noConsts)

describe('mkDiagramWithBoundary', () => {
  it('accepts ordered boundary wires and reports arity; a relation IS a diagram with a boundary', () => {
    const b = new DiagramBuilder()
    const t = b.termNode(b.root, p('\\x. y x'))
    const w0 = b.wire(b.root, [{ node: t, port: { kind: 'output' } }])
    const w1 = b.wire(b.root, [{ node: t, port: { kind: 'freeVar', name: 'y' } }])
    const d = b.build()
    const rel = mkDiagramWithBoundary(d, [w0, w1])
    expect(boundaryArity(rel)).toBe(2)
    expect(rel.boundary).toEqual(['w0', 'w1'])
  })

  it('accepts an empty boundary (a sentence is a 0-ary relation)', () => {
    const b = new DiagramBuilder()
    b.termNode(b.root, p('\\x. x'))
    const rel = mkDiagramWithBoundary(b.build(), [])
    expect(boundaryArity(rel)).toBe(0)
  })

  it('rejects boundary wires that do not exist', () => {
    const b = new DiagramBuilder()
    b.termNode(b.root, p('\\x. x'))
    expect(() => mkDiagramWithBoundary(b.build(), ['ghost']))
      .toThrowError(/boundary wire 'ghost' does not exist/)
  })

  it('rejects duplicate boundary wires', () => {
    const b = new DiagramBuilder()
    const t = b.termNode(b.root, p('\\x. x'))
    const w = b.wire(b.root, [{ node: t, port: { kind: 'output' } }])
    expect(() => mkDiagramWithBoundary(b.build(), [w, w]))
      .toThrowError(/duplicate boundary wire 'w0'/)
  })
})
```

- [ ] **Step 2: Run tests to verify they fail**

Run: `npx vitest run tests/kernel/diagram/boundary.test.ts`
Expected: FAIL — cannot resolve `boundary`.

- [ ] **Step 3: Implement**

`src/kernel/diagram/boundary.ts`:

```ts
import type { Diagram, WireId } from './diagram'
import { DiagramError } from './diagram'

/**
 * A diagram plus an ordered list of boundary wires. One concept, three roles
 * (spec §2.2): rule-statement sides, comprehension instances, and named-
 * relation definition bodies. A relation is exactly a diagram with a boundary;
 * its arity is the boundary length.
 */
export type DiagramWithBoundary = {
  readonly diagram: Diagram
  readonly boundary: readonly WireId[]
}

export function mkDiagramWithBoundary(diagram: Diagram, boundary: readonly WireId[]): DiagramWithBoundary {
  const seen = new Set<WireId>()
  for (const w of boundary) {
    if (diagram.wires[w] === undefined) throw new DiagramError(`boundary wire '${w}' does not exist`)
    if (seen.has(w)) throw new DiagramError(`duplicate boundary wire '${w}'`)
    seen.add(w)
  }
  return Object.freeze({ diagram, boundary: Object.freeze([...boundary]) })
}

export function boundaryArity(d: DiagramWithBoundary): number {
  return d.boundary.length
}
```

- [ ] **Step 4: Verify PASS, full suite, typecheck**

Run: `npx vitest run tests/kernel/diagram/boundary.test.ts && npm test && npm run typecheck`

- [ ] **Step 5: Commit**

```bash
git add src/kernel/diagram/boundary.ts tests/kernel/diagram/boundary.test.ts
git commit -m "feat(kernel): diagrams with ordered boundary wires"
```

---

### Task 7: Public surface

**Files:**
- Create: `src/kernel/diagram/index.ts`

- [ ] **Step 1: Write the barrel**

`src/kernel/diagram/index.ts`:

```ts
export type {
  RegionId, NodeId, WireId, Region, DiagramNode, Port, Endpoint, Wire, Diagram,
} from './diagram'
export { mkDiagram, portKey, requiredPorts, DiagramError } from './diagram'
export { isAncestorOrEqual, cutDepth, polarity } from './regions'
export { DiagramBuilder } from './builder'
export { diagramToJson, diagramFromJson } from './json'
export type { DiagramWithBoundary } from './boundary'
export { mkDiagramWithBoundary, boundaryArity } from './boundary'
```

- [ ] **Step 2: Full gate**

Run: `npm test && npm run typecheck`
Expected: all green (Plan 1's 69 tests plus this plan's new ones); typecheck exit 0.

- [ ] **Step 3: Commit**

```bash
git add src/kernel/diagram/index.ts
git commit -m "feat(kernel): diagram-layer public surface"
```

---

## Completion criteria for this plan

- `npm test` green, `npm run typecheck` clean.
- The diagram layer demonstrates, in its own tests: validating construction with every invariant's violation rejected by name; lines of identity crossing cuts; parity unaffected by bubbles; builder-made diagrams always valid; JSON round-trip with re-validation and loud malformed rejection; boundaries as ordered wire lists.
- No imports from outside `src/kernel/` anywhere under `src/kernel/diagram/`.
- Plan 3 (canonicalization + fingerprints) is written against these real exports.
