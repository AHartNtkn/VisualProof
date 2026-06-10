# Canonicalization + Fingerprints Implementation Plan (Plan 3 of 7)

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** An exact canonical form for diagrams: `diagramFingerprint(d1) === diagramFingerprint(d2)` **iff** d1 and d2 are isomorphic — no hashing, no approximation. Plus `diagramsIsomorphic`, and boundary-pinned fingerprints for `DiagramWithBoundary`.

**Architecture:** Spec §4.3 ("a deterministic, documented, structure-directed canonical form … exact, not a hash-and-hope heuristic"). Algorithm: **individualization-refinement (IR) canonical labeling** over the three object sorts (regions, nodes, wires). Iterated color refinement assigns isomorphism-invariant integer colors; when refinement stalls with ties, branch on each member of the first tied class (individualize, re-refine, recurse) and take the lexicographically minimal serialization over all branches. Exponential worst case, exact always; proof diagrams are small and mostly asymmetric, so refinement alone usually suffices.

**Key semantic decision — positional ports:** a term node's free-variable *names* are internal labels; the relation it denotes depends only on the term with ports taken in first-occurrence order (spec §2.2 constructor semantics). The canonical form therefore renames free ports positionally (`p0, p1, …`) inside the node's *shape key* and refers to ports by position (`out`, `v0`, `v1`, … / `a0`, `a1`, …) in wire endpoints. Fingerprints are thus invariant under consistent per-node free-variable renaming — which preserves semantics — while remaining sensitive to everything that matters (argument order, wiring, scope, parity, arity, binders).

**Boundary pinning:** for `DiagramWithBoundary`, boundary wires receive distinct pinned initial colors in boundary order, so boundary order is significant and never permuted away.

**Isomorphism, precisely:** bijections on regions/nodes/wires preserving: root; region kind, parent, bubble arity; node kind, region, atom binder, and term-node *shape key*; wire scope and endpoint sets (by positional port). The correctness argument (refinement is isomorphism-invariant; the IR tree explores every member of each tied class; min over leaves is therefore a canonical invariant) goes in `docs/kernel/canonicalization.md` (Task 4).

**Tech Stack:** TypeScript (strict), Vitest. No new dependencies. New module directory: `src/kernel/diagram/canonical/`.

**House rules in force:** catch blocks use `e instanceof Error ? e.message : String(e)`; no silent failures; no heuristics (the algorithm is exact; branching explores all candidates); tests are the spec.

---

### Task 1: Positional term shape keys

**Files:**
- Create: `src/kernel/diagram/canonical/shape.ts`
- Test: `tests/kernel/diagram/shape.test.ts`

- [x] **Step 1: Write the failing tests**

`tests/kernel/diagram/shape.test.ts`:

```ts
import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../../src/kernel/term/parse'
import { termShapeKey, positionalPortKey } from '../../../src/kernel/diagram/canonical/shape'

const noConsts = new Set<string>()
const p = (s: string) => parseTerm(s, noConsts)

describe('termShapeKey', () => {
  it('is invariant under free-variable renaming (positional relation identity)', () => {
    expect(termShapeKey(p('y z'))).toBe(termShapeKey(p('a b')))
    expect(termShapeKey(p('y (z y)'))).toBe(termShapeKey(p('z (y z)')))
    expect(termShapeKey(p('\\x. y x'))).toBe(termShapeKey(p('\\q. w q')))
  })

  it('distinguishes different positional relations', () => {
    // one free var used twice vs two distinct free vars
    expect(termShapeKey(p('y y'))).not.toBe(termShapeKey(p('y z')))
    // constants are global names, never renamed
    expect(termShapeKey(p('y'))).not.toBe(termShapeKey(parseTerm('plus', new Set(['plus']))))
    // structure matters
    expect(termShapeKey(p('\\x. x'))).not.toBe(termShapeKey(p('\\x. \\y. x')))
  })

  it('renames ports as p0, p1 in first-occurrence order', () => {
    expect(termShapeKey(p('y z'))).toBe('A(P("p0"),P("p1"))')
    expect(termShapeKey(p('z y'))).toBe('A(P("p0"),P("p1"))') // same positional relation
  })

  it('rejects malformed terms loudly', () => {
    expect(() => termShapeKey({ kind: 'bvar', index: 0 })).toThrowError(/unbound de Bruijn index/)
  })
})

describe('positionalPortKey', () => {
  it('maps output to out, freeVar names to v{first-occurrence index}, args to a{index}', () => {
    const t = p('y (z y)') // first occurrence order: y, z
    expect(positionalPortKey(t, { kind: 'output' })).toBe('out')
    expect(positionalPortKey(t, { kind: 'freeVar', name: 'y' })).toBe('v0')
    expect(positionalPortKey(t, { kind: 'freeVar', name: 'z' })).toBe('v1')
    expect(positionalPortKey(t, { kind: 'arg', index: 3 })).toBe('a3')
  })

  it('throws for a freeVar name not free in the term', () => {
    expect(() => positionalPortKey(p('y'), { kind: 'freeVar', name: 'zz' }))
      .toThrowError(/'zz' is not a free variable of the term/)
  })
})
```

- [x] **Step 2: Run tests to verify they fail**

Run: `npx vitest run tests/kernel/diagram/shape.test.ts`
Expected: FAIL — cannot resolve `canonical/shape`.

- [x] **Step 3: Implement**

`src/kernel/diagram/canonical/shape.ts`:

```ts
import type { Term } from '../../term/term'
import { app, assertWellFormedTerm, cnst, freePorts, lam, port, bvar } from '../../term/term'
import { serializeTerm } from '../../term/serialize'
import type { Port } from '../diagram'
import { DiagramError } from '../diagram'

/**
 * The shape key of a term node: its term with free ports renamed positionally
 * (p0, p1, … in first-occurrence order), serialized. Two term nodes denote the
 * same positional constructor relation iff their shape keys are equal — free
 * variable names are internal labels, not content (spec §2.2).
 */
export function termShapeKey(t: Term): string {
  assertWellFormedTerm(t)
  const order = freePorts(t)
  const rename = new Map(order.map((name, i) => [name, `p${i}`]))
  return serializeTerm(renamePorts(t, rename))
}

function renamePorts(t: Term, rename: ReadonlyMap<string, string>): Term {
  switch (t.kind) {
    case 'port': {
      const next = rename.get(t.name)
      if (next === undefined) {
        throw new DiagramError(`port '${t.name}' missing from rename map; freePorts must cover all ports`)
      }
      return port(next)
    }
    case 'lam': return lam(renamePorts(t.body, rename))
    case 'app': return app(renamePorts(t.fn, rename), renamePorts(t.arg, rename))
    case 'bvar': return bvar(t.index)
    case 'const': return cnst(t.id)
  }
}

/**
 * Positional key for a port: 'out' for the output, 'v{i}' for the free
 * variable at first-occurrence position i, 'a{i}' for atom args. Used by the
 * canonical form so wire endpoints are name-independent.
 */
export function positionalPortKey(termOfNode: Term, p: Port): string {
  switch (p.kind) {
    case 'output': return 'out'
    case 'arg': return `a${p.index}`
    case 'freeVar': {
      const i = freePorts(termOfNode).indexOf(p.name)
      if (i < 0) throw new DiagramError(`'${p.name}' is not a free variable of the term`)
      return `v${i}`
    }
  }
}
```

- [x] **Step 4: Verify PASS, full suite, typecheck**

Run: `npx vitest run tests/kernel/diagram/shape.test.ts && npm test && npm run typecheck`

- [x] **Step 5: Commit**

```bash
git add src/kernel/diagram/canonical/shape.ts tests/kernel/diagram/shape.test.ts
git commit -m "feat(kernel): positional term shape keys for canonicalization"
```

---

### Task 2: The canonical form (refinement + individualization + serialization)

**Files:**
- Create: `src/kernel/diagram/canonical/canonical.ts`
- Test: `tests/kernel/diagram/canonical.test.ts`

This is the core algorithm. The test file covers basic invariance and discrimination; the adversarial battery is Task 4.

- [x] **Step 1: Write the failing tests**

`tests/kernel/diagram/canonical.test.ts`:

```ts
import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../../src/kernel/term/parse'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { canonicalForm } from '../../../src/kernel/diagram/canonical/canonical'

const noConsts = new Set<string>()
const p = (s: string) => parseTerm(s, noConsts)

describe('canonicalForm', () => {
  it('is invariant under construction order (id renaming)', () => {
    // same diagram, two construction orders → different ids, same canonical form
    const b1 = new DiagramBuilder()
    const cut1 = b1.cut(b1.root)
    const t1 = b1.termNode(cut1, p('\\x. x'))
    const s1 = b1.termNode(b1.root, p('\\x. \\y. x'))
    b1.wire(b1.root, [
      { node: s1, port: { kind: 'output' } },
      { node: t1, port: { kind: 'output' } },
    ])
    const b2 = new DiagramBuilder()
    const s2 = b2.termNode(b2.root, p('\\x. \\y. x'))
    const cut2 = b2.cut(b2.root)
    const t2 = b2.termNode(cut2, p('\\x. x'))
    b2.wire(b2.root, [
      { node: t2, port: { kind: 'output' } },
      { node: s2, port: { kind: 'output' } },
    ])
    expect(canonicalForm(b1.build())).toBe(canonicalForm(b2.build()))
  })

  it('is invariant under per-node free-variable renaming', () => {
    const mk = (term: string) => {
      const b = new DiagramBuilder()
      const n = b.termNode(b.root, p(term))
      const m = b.termNode(b.root, p('\\x. x'))
      const names = term.includes('y') ? ['y', 'z'] : ['a', 'b']
      b.wire(b.root, [
        { node: n, port: { kind: 'freeVar', name: names[0]! } },
        { node: m, port: { kind: 'output' } },
      ])
      return b.build()
    }
    expect(canonicalForm(mk('y z'))).toBe(canonicalForm(mk('a b')))
  })

  it('distinguishes wiring differences', () => {
    // X(t, t) with both args on one wire vs X(t, s) on two wires
    const mk = (shared: boolean) => {
      const b = new DiagramBuilder()
      const bub = b.bubble(b.root, 2)
      const t = b.termNode(bub, p('\\x. x'))
      const a = b.atom(bub, bub)
      if (shared) {
        b.wire(bub, [
          { node: t, port: { kind: 'output' } },
          { node: a, port: { kind: 'arg', index: 0 } },
          { node: a, port: { kind: 'arg', index: 1 } },
        ])
      } else {
        b.wire(bub, [
          { node: t, port: { kind: 'output' } },
          { node: a, port: { kind: 'arg', index: 0 } },
        ])
      }
      return b.build()
    }
    expect(canonicalForm(mk(true))).not.toBe(canonicalForm(mk(false)))
  })

  it('distinguishes cut from bubble and arity from arity', () => {
    const mk = (kind: 'cut' | 'bubble', arity?: number) => {
      const b = new DiagramBuilder()
      if (kind === 'cut') b.cut(b.root)
      else b.bubble(b.root, arity!)
      return b.build()
    }
    expect(canonicalForm(mk('cut'))).not.toBe(canonicalForm(mk('bubble', 0)))
    expect(canonicalForm(mk('bubble', 0))).not.toBe(canonicalForm(mk('bubble', 1)))
  })

  it('handles symmetric diagrams via individualization (two identical disconnected cuts)', () => {
    const mk = (swap: boolean) => {
      const b = new DiagramBuilder()
      const first = b.cut(b.root)
      const second = b.cut(b.root)
      const [x, y] = swap ? [second, first] : [first, second]
      b.termNode(x, p('\\x. x'))
      b.termNode(y, p('\\x. x'))
      return b.build()
    }
    // refinement alone cannot split the two cuts; individualization must, and
    // the result must not depend on construction order
    expect(canonicalForm(mk(false))).toBe(canonicalForm(mk(true)))
  })

  it('distinguishes wire scope (same endpoints, different quantifier location)', () => {
    const mk = (scopeAtRoot: boolean) => {
      const b = new DiagramBuilder()
      const cut = b.cut(b.root)
      const t = b.termNode(cut, p('\\x. x'))
      b.wire(scopeAtRoot ? b.root : cut, [{ node: t, port: { kind: 'output' } }])
      return b.build()
    }
    expect(canonicalForm(mk(true))).not.toBe(canonicalForm(mk(false)))
  })

  it('pins boundary wires by order when given', () => {
    const mk = () => {
      const b = new DiagramBuilder()
      const n = b.termNode(b.root, p('y x'))
      const wOut = b.wire(b.root, [{ node: n, port: { kind: 'output' } }])
      const wY = b.wire(b.root, [{ node: n, port: { kind: 'freeVar', name: 'y' } }])
      return { d: b.build(), wOut, wY }
    }
    const a = mk()
    const b2 = mk()
    expect(canonicalForm(a.d, [a.wOut, a.wY])).toBe(canonicalForm(b2.d, [b2.wOut, b2.wY]))
    expect(canonicalForm(a.d, [a.wOut, a.wY])).not.toBe(canonicalForm(a.d, [a.wY, a.wOut]))
  })

  it('throws on pinned wires that do not exist', () => {
    const b = new DiagramBuilder()
    b.termNode(b.root, p('\\x. x'))
    expect(() => canonicalForm(b.build(), ['ghost'])).toThrowError(/pinned wire 'ghost' does not exist/)
  })

  it('throws on duplicate pinned wires', () => {
    const b = new DiagramBuilder()
    const n = b.termNode(b.root, p('\\x. x'))
    const w = b.wire(b.root, [{ node: n, port: { kind: 'output' } }])
    expect(() => canonicalForm(b.build(), [w, w])).toThrowError(/duplicate pinned wire 'w0'/)
  })
})
```

- [x] **Step 2: Run tests to verify they fail**

Run: `npx vitest run tests/kernel/diagram/canonical.test.ts`
Expected: FAIL — cannot resolve `canonical/canonical`.

- [x] **Step 3: Implement**

`src/kernel/diagram/canonical/canonical.ts`:

```ts
import type { Diagram, NodeId, RegionId, WireId } from '../diagram'
import { DiagramError } from '../diagram'
import { freePorts } from '../../term/term'
import { termShapeKey, positionalPortKey } from './shape'

/**
 * Exact canonical form by individualization-refinement.
 *
 * Colors: every region, node, and wire carries an integer color. Initial
 * colors come from isomorphism-invariant local content (kind, arity, shape
 * key, boundary pin). Refinement rounds replace each object's color with the
 * rank of its signature — old color plus the colors of its neighborhood —
 * until the number of color classes stabilizes. Old colors prefix every
 * signature, so refinement only ever splits classes, never merges: the class
 * count is monotone and the loop terminates.
 *
 * If classes remain tied (genuine symmetry), pick the first tied class
 * (smallest color) and branch: individualize each member in turn, re-refine,
 * recurse, and keep the lexicographically smallest serialization. Every
 * member of the tied class is explored, so the minimum is invariant under
 * isomorphism — this is what makes the form exact rather than heuristic.
 * Worst case exponential; proof diagrams are small.
 *
 * Pinned wires (the boundary of a DiagramWithBoundary) get distinct initial
 * colors in pin order, so boundary order is significant.
 */
export function canonicalForm(d: Diagram, pinnedWires: readonly WireId[] = []): string {
  const seenPins = new Set<string>()
  for (const w of pinnedWires) {
    if (d.wires[w] === undefined) throw new DiagramError(`pinned wire '${w}' does not exist`)
    if (seenPins.has(w)) throw new DiagramError(`duplicate pinned wire '${w}'`)
    seenPins.add(w)
  }
  const idx = buildIndex(d, pinnedWires)
  const colors = refine(idx, initialColors(idx))
  return search(idx, colors)
}

type Index = {
  readonly regionIds: readonly RegionId[]
  readonly nodeIds: readonly NodeId[]
  readonly wireIds: readonly WireId[]
  readonly regionKindKey: ReadonlyMap<RegionId, string>
  readonly parentOf: ReadonlyMap<RegionId, RegionId | null>
  readonly childrenOf: ReadonlyMap<RegionId, readonly RegionId[]>
  readonly nodesIn: ReadonlyMap<RegionId, readonly NodeId[]>
  readonly wiresScoped: ReadonlyMap<RegionId, readonly WireId[]>
  readonly nodeContentKey: ReadonlyMap<NodeId, string>
  readonly nodeRegion: ReadonlyMap<NodeId, RegionId>
  readonly nodeBinder: ReadonlyMap<NodeId, RegionId | null>
  readonly nodePortOrder: ReadonlyMap<NodeId, readonly string[]>
  readonly nodePortWire: ReadonlyMap<NodeId, ReadonlyMap<string, WireId>>
  readonly wireScope: ReadonlyMap<WireId, RegionId>
  readonly wireEndpoints: ReadonlyMap<WireId, readonly { node: NodeId; pkey: string }[]>
  readonly pinOf: ReadonlyMap<WireId, number>
}

function buildIndex(d: Diagram, pinned: readonly WireId[]): Index {
  const regionIds = Object.keys(d.regions)
  const nodeIds = Object.keys(d.nodes)
  const wireIds = Object.keys(d.wires)

  const regionKindKey = new Map<RegionId, string>()
  const parentOf = new Map<RegionId, RegionId | null>()
  const childrenOf = new Map<RegionId, RegionId[]>()
  const nodesIn = new Map<RegionId, NodeId[]>()
  const wiresScoped = new Map<RegionId, WireId[]>()
  for (const id of regionIds) {
    childrenOf.set(id, [])
    nodesIn.set(id, [])
    wiresScoped.set(id, [])
  }
  for (const id of regionIds) {
    const r = d.regions[id]!
    regionKindKey.set(id, r.kind === 'bubble' ? `bubble/${r.arity}` : r.kind)
    if (r.kind === 'sheet') {
      parentOf.set(id, null)
    } else {
      parentOf.set(id, r.parent)
      childrenOf.get(r.parent)!.push(id)
    }
  }

  const nodeContentKey = new Map<NodeId, string>()
  const nodeRegion = new Map<NodeId, RegionId>()
  const nodeBinder = new Map<NodeId, RegionId | null>()
  const nodePortOrder = new Map<NodeId, string[]>()
  const nodePortWire = new Map<NodeId, Map<string, WireId>>()
  for (const id of nodeIds) {
    const n = d.nodes[id]!
    nodeRegion.set(id, n.region)
    nodesIn.get(n.region)!.push(id)
    nodePortWire.set(id, new Map())
    if (n.kind === 'term') {
      nodeContentKey.set(id, `term:${termShapeKey(n.term)}`)
      nodeBinder.set(id, null)
      // positional v-keys: one per free port, already in first-occurrence order
      nodePortOrder.set(id, ['out', ...freePorts(n.term).map((_, i) => `v${i}`)])
    } else {
      nodeContentKey.set(id, 'atom')
      nodeBinder.set(id, n.binder)
      const binder = d.regions[n.binder]!
      const arity = binder.kind === 'bubble' ? binder.arity : 0
      nodePortOrder.set(id, Array.from({ length: arity }, (_, i) => `a${i}`))
    }
  }

  const wireScope = new Map<WireId, RegionId>()
  const wireEndpoints = new Map<WireId, { node: NodeId; pkey: string }[]>()
  for (const id of wireIds) {
    const w = d.wires[id]!
    wireScope.set(id, w.scope)
    wiresScoped.get(w.scope)!.push(id)
    const eps = w.endpoints.map((ep) => {
      const n = d.nodes[ep.node]!
      let pkey: string
      if (n.kind === 'term') {
        pkey = positionalPortKey(n.term, ep.port)
      } else if (ep.port.kind === 'arg') {
        pkey = `a${ep.port.index}`
      } else {
        // mkDiagram's port-membership check makes this unreachable: atoms have
        // only arg ports. Throw rather than fabricate.
        throw new DiagramError(`atom '${ep.node}' cannot carry port '${ep.port.kind}'`)
      }
      nodePortWire.get(ep.node)!.set(pkey, id)
      return { node: ep.node, pkey }
    })
    wireEndpoints.set(id, eps)
  }

  const pinOf = new Map<WireId, number>()
  pinned.forEach((w, i) => pinOf.set(w, i))

  return {
    regionIds, nodeIds, wireIds, regionKindKey, parentOf, childrenOf, nodesIn,
    wiresScoped, nodeContentKey, nodeRegion, nodeBinder, nodePortOrder,
    nodePortWire, wireScope, wireEndpoints, pinOf,
  }
}

type Colors = {
  readonly region: ReadonlyMap<RegionId, number>
  readonly node: ReadonlyMap<NodeId, number>
  readonly wire: ReadonlyMap<WireId, number>
}

function classCount(c: Colors): number {
  return new Set([...c.region.values(), ...c.node.values(), ...c.wire.values()]).size
}

function rankSignatures(entries: [string, string][]): Map<string, number> {
  const distinct = [...new Set(entries.map(([, sig]) => sig))].sort()
  const rank = new Map(distinct.map((s, i) => [s, i]))
  const out = new Map<string, number>()
  for (const [id, sig] of entries) out.set(id, rank.get(sig)!)
  return out
}

function initialColors(idx: Index): Colors {
  const entries: [string, string][] = []
  for (const id of idx.regionIds) entries.push([`R${id}`, `R|${idx.regionKindKey.get(id)!}`])
  for (const id of idx.nodeIds) entries.push([`N${id}`, `N|${idx.nodeContentKey.get(id)!}`])
  for (const id of idx.wireIds) {
    const pin = idx.pinOf.get(id)
    entries.push([`W${id}`, `W|${pin === undefined ? 'w' : `pin${pin}`}`])
  }
  const ranked = rankSignatures(entries)
  return {
    region: new Map(idx.regionIds.map((id) => [id, ranked.get(`R${id}`)!])),
    node: new Map(idx.nodeIds.map((id) => [id, ranked.get(`N${id}`)!])),
    wire: new Map(idx.wireIds.map((id) => [id, ranked.get(`W${id}`)!])),
  }
}

function refineOnce(idx: Index, c: Colors): Colors {
  const entries: [string, string][] = []
  for (const id of idx.regionIds) {
    const parent = idx.parentOf.get(id)
    const children = idx.childrenOf.get(id)!.map((x) => c.region.get(x)!).sort((a, b) => a - b)
    const nodes = idx.nodesIn.get(id)!.map((x) => c.node.get(x)!).sort((a, b) => a - b)
    const wires = idx.wiresScoped.get(id)!.map((x) => c.wire.get(x)!).sort((a, b) => a - b)
    entries.push([`R${id}`,
      `R|${c.region.get(id)!}|p:${parent === null ? '-' : c.region.get(parent)!}|c:${children.join(',')}|n:${nodes.join(',')}|w:${wires.join(',')}`])
  }
  for (const id of idx.nodeIds) {
    const binder = idx.nodeBinder.get(id)
    const ports = idx.nodePortOrder.get(id)!
      .map((pk) => `${pk}=${c.wire.get(idx.nodePortWire.get(id)!.get(pk)!)!}`)
    entries.push([`N${id}`,
      `N|${c.node.get(id)!}|r:${c.region.get(idx.nodeRegion.get(id)!)!}|b:${binder == null ? '-' : c.region.get(binder)!}|${ports.join(',')}`])
  }
  for (const id of idx.wireIds) {
    const eps = idx.wireEndpoints.get(id)!
      .map((ep) => `${c.node.get(ep.node)!}.${ep.pkey}`)
      .sort()
    entries.push([`W${id}`,
      `W|${c.wire.get(id)!}|s:${c.region.get(idx.wireScope.get(id)!)!}|e:${eps.join(',')}`])
  }
  const ranked = rankSignatures(entries)
  return {
    region: new Map(idx.regionIds.map((id) => [id, ranked.get(`R${id}`)!])),
    node: new Map(idx.nodeIds.map((id) => [id, ranked.get(`N${id}`)!])),
    wire: new Map(idx.wireIds.map((id) => [id, ranked.get(`W${id}`)!])),
  }
}

function refine(idx: Index, c0: Colors): Colors {
  let c = c0
  let classes = classCount(c)
  for (;;) {
    const next = refineOnce(idx, c)
    const nextClasses = classCount(next)
    if (nextClasses === classes) return next
    c = next
    classes = nextClasses
  }
}

/** First tied class: members sharing the smallest tied color, in a fixed sort order. */
function firstTiedClass(idx: Index, c: Colors): { sort: 'region' | 'node' | 'wire'; members: string[] } | null {
  let best: { color: number; sort: 'region' | 'node' | 'wire'; members: string[] } | null = null
  const consider = (sort: 'region' | 'node' | 'wire', m: ReadonlyMap<string, number>) => {
    const byColor = new Map<number, string[]>()
    for (const [id, col] of m) {
      const arr = byColor.get(col)
      if (arr === undefined) byColor.set(col, [id])
      else arr.push(id)
    }
    for (const [col, members] of byColor) {
      if (members.length > 1 && (best === null || col < best.color)) {
        best = { color: col, sort, members: members.sort() }
      }
    }
  }
  // colors are globally ranked across sorts, so comparing color values across
  // sorts is well-defined; sort identity rides along for map selection only
  consider('region', c.region)
  consider('node', c.node)
  consider('wire', c.wire)
  return best === null ? null : { sort: best.sort, members: best.members }
}

function individualize(c: Colors, sort: 'region' | 'node' | 'wire', id: string): Colors {
  const bump = classCount(c)
  const clone = {
    region: new Map(c.region),
    node: new Map(c.node),
    wire: new Map(c.wire),
  }
  clone[sort].set(id, bump)
  return clone
}

function search(idx: Index, c: Colors): string {
  const tied = firstTiedClass(idx, c)
  if (tied === null) return serializeWith(idx, c)
  let best: string | null = null
  for (const member of tied.members) {
    const s = search(idx, refine(idx, individualize(c, tied.sort, member)))
    if (best === null || s < best) best = s
  }
  return best!
}

function serializeWith(idx: Index, c: Colors): string {
  const regionOrd = ordinalize(idx.regionIds, c.region)
  const nodeOrd = ordinalize(idx.nodeIds, c.node)
  const wireOrd = ordinalize(idx.wireIds, c.wire)
  const lines: string[] = []
  for (const id of sortByOrd(idx.regionIds, regionOrd)) {
    const parent = idx.parentOf.get(id)
    lines.push(`r${regionOrd.get(id)!}:${idx.regionKindKey.get(id)!}:p=${parent === null ? '-' : `r${regionOrd.get(parent)!}`}`)
  }
  for (const id of sortByOrd(idx.nodeIds, nodeOrd)) {
    const binder = idx.nodeBinder.get(id)
    lines.push(`n${nodeOrd.get(id)!}:${idx.nodeContentKey.get(id)!}:r=r${regionOrd.get(idx.nodeRegion.get(id)!)!}${binder == null ? '' : `:b=r${regionOrd.get(binder)!}`}`)
  }
  for (const id of sortByOrd(idx.wireIds, wireOrd)) {
    const pin = idx.pinOf.get(id)
    const eps = idx.wireEndpoints.get(id)!
      .map((ep) => `n${nodeOrd.get(ep.node)!}.${ep.pkey}`)
      .sort()
    lines.push(`w${wireOrd.get(id)!}:${pin === undefined ? '' : `pin${pin}:`}s=r${regionOrd.get(idx.wireScope.get(id)!)!}:e=${eps.join(',')}`)
  }
  return lines.join('\n')
}

function ordinalize(ids: readonly string[], colors: ReadonlyMap<string, number>): Map<string, number> {
  const sorted = [...ids].sort((a, b) => colors.get(a)! - colors.get(b)!)
  return new Map(sorted.map((id, i) => [id, i]))
}

function sortByOrd(ids: readonly string[], ord: ReadonlyMap<string, number>): string[] {
  return [...ids].sort((a, b) => ord.get(a)! - ord.get(b)!)
}
```

Note on the discrete-partition serialization precondition: `search` only calls `serializeWith` when `firstTiedClass` returns null, i.e. every color class is a singleton, so the ordinal maps are total orders and the serialization is deterministic.

Transcription note (from execution): four sites in this reference block do not typecheck under the project's strict tsconfig as written — `Map.get` on a nullable parent needs an undefined re-check after narrowing, `firstTiedClass`'s unused `idx` parameter must be `_idx`, and the closure-mutated nullable `best` defeats TS narrowing and needs a non-nullable restructure. The committed `src/kernel/diagram/canonical/canonical.ts` is the authoritative form; a differential test confirmed it byte-identical in output to this reference on all probe diagrams.

- [x] **Step 4: Verify PASS, full suite, typecheck**

Run: `npx vitest run tests/kernel/diagram/canonical.test.ts && npm test && npm run typecheck`

- [x] **Step 5: Commit**

```bash
git add src/kernel/diagram/canonical/canonical.ts tests/kernel/diagram/canonical.test.ts
git commit -m "feat(kernel): exact canonical form via individualization-refinement"
```

---

### Task 3: Fingerprint API

**Files:**
- Create: `src/kernel/diagram/canonical/fingerprint.ts`
- Test: `tests/kernel/diagram/fingerprint.test.ts`

- [x] **Step 1: Write the failing tests**

`tests/kernel/diagram/fingerprint.test.ts`:

```ts
import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../../src/kernel/term/parse'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { mkDiagramWithBoundary } from '../../../src/kernel/diagram/boundary'
import {
  diagramFingerprint, boundaryFingerprint, diagramsIsomorphic,
} from '../../../src/kernel/diagram/canonical/fingerprint'

const noConsts = new Set<string>()
const p = (s: string) => parseTerm(s, noConsts)

function pair() {
  const mk = (swap: boolean) => {
    const b = new DiagramBuilder()
    const first = b.cut(b.root)
    const second = b.cut(b.root)
    const [x, y] = swap ? [second, first] : [first, second]
    b.termNode(x, p('\\x. x'))
    b.termNode(y, p('\\x. \\y. x'))
    return b.build()
  }
  return [mk(false), mk(true)] as const
}

describe('diagramFingerprint and diagramsIsomorphic', () => {
  it('equal fingerprints iff isomorphic', () => {
    const [d1, d2] = pair()
    expect(diagramFingerprint(d1)).toBe(diagramFingerprint(d2))
    expect(diagramsIsomorphic(d1, d2)).toBe(true)

    const b = new DiagramBuilder()
    b.cut(b.root)
    const d3 = b.build()
    expect(diagramFingerprint(d1)).not.toBe(diagramFingerprint(d3))
    expect(diagramsIsomorphic(d1, d3)).toBe(false)
  })

  it('size shortcut never changes the answer: unequal sizes and equal-size non-isomorphic both reject', () => {
    const b1 = new DiagramBuilder()
    b1.cut(b1.root)
    const b2 = new DiagramBuilder()
    b2.cut(b2.root)
    b2.cut(b2.root)
    expect(diagramsIsomorphic(b1.build(), b2.build())).toBe(false)

    // equal counts, different content: the shortcut cannot fire; the full
    // canonical comparison must reject
    const c1 = new DiagramBuilder()
    c1.termNode(c1.cut(c1.root), p('\\x. x'))
    const c2 = new DiagramBuilder()
    c2.termNode(c2.cut(c2.root), p('\\x. \\y. x'))
    expect(diagramsIsomorphic(c1.build(), c2.build())).toBe(false)
  })
})

describe('boundaryFingerprint', () => {
  it('is order-sensitive and id-invariant', () => {
    const mk = () => {
      const b = new DiagramBuilder()
      const n = b.termNode(b.root, p('y x'))
      const wOut = b.wire(b.root, [{ node: n, port: { kind: 'output' } }])
      const wY = b.wire(b.root, [{ node: n, port: { kind: 'freeVar', name: 'y' } }])
      return { d: b.build(), wOut, wY }
    }
    const a = mk()
    const c = mk()
    const fa = boundaryFingerprint(mkDiagramWithBoundary(a.d, [a.wOut, a.wY]))
    const fc = boundaryFingerprint(mkDiagramWithBoundary(c.d, [c.wOut, c.wY]))
    const faRev = boundaryFingerprint(mkDiagramWithBoundary(a.d, [a.wY, a.wOut]))
    expect(fa).toBe(fc)
    expect(fa).not.toBe(faRev)
  })
})
```

- [x] **Step 2: Run tests to verify they fail**

Run: `npx vitest run tests/kernel/diagram/fingerprint.test.ts`
Expected: FAIL — cannot resolve `canonical/fingerprint`.

- [x] **Step 3: Implement**

`src/kernel/diagram/canonical/fingerprint.ts`:

```ts
import type { Diagram } from '../diagram'
import type { DiagramWithBoundary } from '../boundary'
import { canonicalForm } from './canonical'

/**
 * Content fingerprint: the canonical serialization itself. Exact by
 * construction — equal strings iff isomorphic diagrams. If profiling ever
 * shows fingerprint length matters for storage, hash AT THE STORAGE LAYER and
 * keep this exact string as the comparison key; never compare hashes for
 * soundness-relevant equality.
 */
export function diagramFingerprint(d: Diagram): string {
  return canonicalForm(d)
}

/**
 * Boundary-pinned fingerprint: boundary order is significant — pinned wires
 * carry 'pin{i}:' markers in the canonical form, so two boundaries differing
 * only in order fingerprint differently. With an EMPTY boundary this equals
 * diagramFingerprint of the same diagram, intentionally: a 0-ary relation is
 * a sentence. No cross-API collision is possible otherwise, since any
 * non-empty boundary puts at least one pin marker in the string and unpinned
 * forms never contain one.
 */
export function boundaryFingerprint(dwb: DiagramWithBoundary): string {
  return canonicalForm(dwb.diagram, dwb.boundary)
}

export function diagramsIsomorphic(d1: Diagram, d2: Diagram): boolean {
  if (
    Object.keys(d1.regions).length !== Object.keys(d2.regions).length ||
    Object.keys(d1.nodes).length !== Object.keys(d2.nodes).length ||
    Object.keys(d1.wires).length !== Object.keys(d2.wires).length
  ) {
    return false
  }
  return canonicalForm(d1) === canonicalForm(d2)
}
```

- [x] **Step 4: Verify PASS, full suite, typecheck**

- [x] **Step 5: Commit**

```bash
git add src/kernel/diagram/canonical/fingerprint.ts tests/kernel/diagram/fingerprint.test.ts
git commit -m "feat(kernel): diagram and boundary fingerprints over the canonical form"
```

---

### Task 4: Adversarial battery + algorithm documentation

**Files:**
- Test: `tests/kernel/diagram/canonical-adversarial.test.ts`
- Create: `docs/kernel/canonicalization.md`

- [x] **Step 1: Write the adversarial tests** (these must pass against Task 2's implementation; any failure is an algorithm bug to fix test-first)

`tests/kernel/diagram/canonical-adversarial.test.ts`:

```ts
import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../../src/kernel/term/parse'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { canonicalForm } from '../../../src/kernel/diagram/canonical/canonical'

const noConsts = new Set<string>()
const p = (s: string) => parseTerm(s, noConsts)

describe('canonicalForm adversarial battery', () => {
  it('distinguishes atom binder depth (inner vs outer bubble of equal arity)', () => {
    const mk = (inner: boolean) => {
      const b = new DiagramBuilder()
      const outer = b.bubble(b.root, 1)
      const innerB = b.bubble(outer, 1)
      b.atom(innerB, inner ? innerB : outer)
      return b.build()
    }
    expect(canonicalForm(mk(true))).not.toBe(canonicalForm(mk(false)))
  })

  it('distinguishes which of two same-shape nodes a third connects to, under symmetry', () => {
    // two identical cuts each holding `\x. y x`; a shared term node wires to
    // the free var of ONE of them; swapping which one must not matter (iso),
    // but wiring to BOTH must differ from wiring to one
    const mk = (both: boolean) => {
      const b = new DiagramBuilder()
      const c1 = b.cut(b.root)
      const c2 = b.cut(b.root)
      const n1 = b.termNode(c1, p('\\x. y x'))
      const n2 = b.termNode(c2, p('\\x. y x'))
      const hub = b.termNode(b.root, p('\\x. x'))
      if (both) {
        b.wire(b.root, [
          { node: hub, port: { kind: 'output' } },
          { node: n1, port: { kind: 'freeVar', name: 'y' } },
          { node: n2, port: { kind: 'freeVar', name: 'y' } },
        ])
      } else {
        b.wire(b.root, [
          { node: hub, port: { kind: 'output' } },
          { node: n1, port: { kind: 'freeVar', name: 'y' } },
        ])
      }
      return b.build()
    }
    const one = mk(false)
    const two = mk(true)
    expect(canonicalForm(one)).not.toBe(canonicalForm(two))
    // and the one-sided version is invariant under which side is chosen
    const mkOther = () => {
      const b = new DiagramBuilder()
      const c1 = b.cut(b.root)
      const c2 = b.cut(b.root)
      const n1 = b.termNode(c1, p('\\x. y x'))
      const n2 = b.termNode(c2, p('\\x. y x'))
      const hub = b.termNode(b.root, p('\\x. x'))
      b.wire(b.root, [
        { node: hub, port: { kind: 'output' } },
        { node: n2, port: { kind: 'freeVar', name: 'y' } },
      ])
      void n1
      return b.build()
    }
    expect(canonicalForm(one)).toBe(canonicalForm(mkOther()))
  })

  it('distinguishes arg-position wiring on an atom (X(s,t) vs X(t,s))', () => {
    const mk = (swapped: boolean) => {
      const b = new DiagramBuilder()
      const bub = b.bubble(b.root, 2)
      const s = b.termNode(bub, p('\\x. x'))
      const t = b.termNode(bub, p('\\x. \\y. x'))
      const a = b.atom(bub, bub)
      b.wire(bub, [
        { node: s, port: { kind: 'output' } },
        { node: a, port: { kind: 'arg', index: swapped ? 1 : 0 } },
      ])
      b.wire(bub, [
        { node: t, port: { kind: 'output' } },
        { node: a, port: { kind: 'arg', index: swapped ? 0 : 1 } },
      ])
      return b.build()
    }
    expect(canonicalForm(mk(false))).not.toBe(canonicalForm(mk(true)))
  })

  it('three-way symmetry: triple identical cuts canonicalize order-independently', () => {
    const perms: number[][] = [
      [0, 1, 2], [0, 2, 1], [1, 0, 2], [1, 2, 0], [2, 0, 1], [2, 1, 0],
    ]
    const forms = perms.map((perm) => {
      const b = new DiagramBuilder()
      const cuts = [b.cut(b.root), b.cut(b.root), b.cut(b.root)]
      const contents = [p('\\x. x'), p('\\x. \\y. x'), p('\\x. \\y. y')]
      perm.forEach((ci, i) => b.termNode(cuts[ci]!, contents[i]!))
      return canonicalForm(b.build())
    })
    expect(new Set(forms).size).toBe(1)
  })

  it('zero-endpoint wires count and scope placement matter', () => {
    const mk = (count: number) => {
      const b = new DiagramBuilder()
      const cut = b.cut(b.root)
      for (let i = 0; i < count; i++) b.wire(cut, [])
      return b.build()
    }
    expect(canonicalForm(mk(1))).not.toBe(canonicalForm(mk(2)))
  })

  it('term content distinguishes beyond shape of wiring', () => {
    const mk = (term: string) => {
      const b = new DiagramBuilder()
      b.termNode(b.root, p(term))
      return b.build()
    }
    expect(canonicalForm(mk('\\x. x'))).not.toBe(canonicalForm(mk('\\x. \\y. x')))
  })
})
```

- [x] **Step 2: Run; all must pass.** Any failure is an algorithm bug: write it up, fix `canonical.ts` test-first against the failing case, and report.

- [x] **Step 3: Write the algorithm documentation**

`docs/kernel/canonicalization.md` — must contain, in prose: the object model (three sorts, what isomorphism preserves); the positional-port decision and its semantic justification; initial coloring; the refinement signature for each sort and why including the previous color makes refinement monotone (split-only) and terminating; the individualization branch rule (first tied class, all members explored) and why taking the minimum over all branches yields an isomorphism invariant; the discrete-partition precondition of serialization; boundary pinning; complexity (exponential worst case, exact always — explicitly: this is the no-heuristics trade); and the storage note (hash only at the storage layer, never for soundness comparisons).

- [x] **Step 4: Full gate**

Run: `npm test && npm run typecheck`

- [x] **Step 5: Commit**

```bash
git add tests/kernel/diagram/canonical-adversarial.test.ts docs/kernel/canonicalization.md
git commit -m "test(kernel): adversarial canonicalization battery; document the algorithm"
```

---

### Task 5: Public surface

**Files:**
- Modify: `src/kernel/diagram/index.ts`

- [x] **Step 1: Extend the barrel** — append to `src/kernel/diagram/index.ts`:

```ts
export { termShapeKey, positionalPortKey } from './canonical/shape'
export { canonicalForm } from './canonical/canonical'
export { diagramFingerprint, boundaryFingerprint, diagramsIsomorphic } from './canonical/fingerprint'
```

- [x] **Step 2: Full gate** — `npm test && npm run typecheck`; verify every barrel export exists.

- [x] **Step 3: Commit**

```bash
git add src/kernel/diagram/index.ts
git commit -m "feat(kernel): canonicalization public surface"
```

---

## Completion criteria for this plan

- `npm test` green, `npm run typecheck` clean.
- Demonstrated in tests: id/order invariance; free-variable-renaming invariance; symmetric diagrams (2-way and 3-way) canonicalize order-independently via individualization; discrimination of wiring, arg positions, scopes, binder depth, kinds, arities, term content, zero-endpoint wire counts; boundary order significance.
- `docs/kernel/canonicalization.md` documents the algorithm with the correctness argument (spec §4.3's "documented" requirement).
- Plan 4 (foundational rules + matching) is written against these real exports.

## Carried obligations (from Plan 2's final review)

- Plan 4 must resolve the boundary-wire-scope question documented in `boundary.ts` (splice semantics; reject loudly if non-root-scoped boundaries are unspliceable).
- The mechanical forbidden-import check promised by spec §4.2 still does not exist; add it no later than the plan that introduces a second package (likely Plan 6).
