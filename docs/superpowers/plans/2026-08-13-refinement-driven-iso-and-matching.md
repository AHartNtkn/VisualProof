# Refinement-Driven Isomorphism and Matching Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Replace the exhaustive canonical-labeling equality (`explore.ts`) and the factorial occurrence matcher (`match.ts`) with color-refinement engines that never branch on practical diagrams, keeping enumeration only as the mathematically forced backstop.

**Architecture:** A shared joint-refinement engine colors one or two diagrams from content only. Pairwise isomorphism reads a verified bijection off discrete colors, individualizing only at residual tied classes (dormant on orbit-clean diagrams). Canonical labeling survives solely for definition argument order. The occurrence matcher becomes candidate-set constraint propagation plus most-constrained-first search.

**Tech Stack:** TypeScript (strict), vitest (`npm test` = `vitest run --config vitest.config.ts`), no new dependencies.

**Spec:** `docs/superpowers/specs/2026-08-13-refinement-driven-iso-and-matching-design.md`

## Global Constraints

- Every commit: `npm run typecheck` (tsc --noEmit) and `npm test` green. The physics suite is NOT verification (repo policy) — never run it as such.
- Run a single test file with: `npx vitest run tests/kernel/diagram/iso.test.ts --config vitest.config.ts`
- No dead code, no re-exports for compatibility, no "legacy" anything. Old API call sites are converted, then the old API is deleted.
- `git add` only the files you touched (shared-tree rule). Commit immediately after each task's verification.
- All new code lives under `src/kernel/diagram/canonical/` and `src/kernel/diagram/subgraph/`; tests under `tests/kernel/diagram/`.
- Domain vocabulary (keep names exactly): regions (sheet root + nested cuts), nodes (`atom` | `ref` | `identity`), wires (hyperedges with `endpoints: {node, port}[]`), pins (ordered boundary wire list of an open diagram; repeats legal). Identity incidence indices are storage-only, never semantic.

**Spec amendment carried by this plan (flagged at plan review):** spec §6 says "host is refined once (unseeded)". Whole-host 1-WL colors are NOT a sound candidate filter for fragment matching (a boundary-adjacent pattern element's image color depends on host context outside the occurrence), and using them would prune real occurrences. The sound host-side invariant computed once is the nested-cut subtree fingerprint (exact by the occurrence contract). Task 7 implements that and amends the spec sentence.

---

### Task 1: Shared refinement engine

**Files:**
- Create: `src/kernel/diagram/canonical/refine.ts`
- Test: `tests/kernel/diagram/refine.test.ts`

**Interfaces:**
- Consumes: `Diagram`, `DiagramError`, `Port` from `../diagram`; `sigKey` from `../sig`.
- Produces (later tasks rely on these exact names):
  - `type Sort = 'region' | 'node' | 'wire'`
  - `type Mark = { readonly side: number; readonly sort: Sort; readonly id: string; readonly token: number }`
  - `type RefinementSide = { readonly diagram: Diagram; readonly pins: readonly WireId[] }`
  - `type SideColors = { readonly region: ReadonlyMap<RegionId, number>; readonly node: ReadonlyMap<NodeId, number>; readonly wire: ReadonlyMap<WireId, number> }`
  - `type RefineIndex` — same fields as today's `ExploreIndex` (explore.ts:74–92)
  - `buildRefineIndex(d: Diagram, pins: readonly WireId[]): RefineIndex`
  - `refineJointly(sides: readonly RefinementSide[], marks?: readonly Mark[]): SideColors[]`

- [ ] **Step 1: Write the failing test**

```ts
// tests/kernel/diagram/refine.test.ts
import { describe, expect, it } from 'vitest'
import { mkDiagram } from '../../../src/kernel/diagram/diagram'
import { refineJointly } from '../../../src/kernel/diagram/canonical/refine'
import { IOTA, relSig } from '../../../src/kernel/diagram/sig'

const rel1 = relSig([IOTA])

/** P(x) with a root pin holding the head wire. Ids parameterized. */
function atomGraph(ids: { atom: string; pin: string; head: string; value: string; valuePin: string }) {
  return mkDiagram({
    root: 'root',
    regions: { root: { kind: 'sheet' } },
    nodes: {
      [ids.atom]: { kind: 'atom', region: 'root', sig: rel1 },
      [ids.pin]: { kind: 'identity', region: 'root', sig: rel1, arity: 1 },
      [ids.valuePin]: { kind: 'identity', region: 'root', sig: IOTA, arity: 1 },
    },
    wires: {
      [ids.head]: {
        sig: rel1,
        endpoints: [
          { node: ids.atom, port: { kind: 'head' } },
          { node: ids.pin, port: { kind: 'identity', index: 0 } },
        ],
      },
      [ids.value]: {
        sig: IOTA,
        endpoints: [
          { node: ids.atom, port: { kind: 'arg', index: 0 } },
          { node: ids.valuePin, port: { kind: 'identity', index: 0 } },
        ],
      },
    },
  })
}

describe('joint refinement', () => {
  it('gives corresponding elements of isomorphic diagrams equal colors', () => {
    const a = atomGraph({ atom: 'a', pin: 'p', head: 'h', value: 'v', valuePin: 'q' })
    const b = atomGraph({ atom: 'x', pin: 'y', head: 'z', value: 'w', valuePin: 'u' })
    const [ca, cb] = refineJointly([
      { diagram: a, pins: [] },
      { diagram: b, pins: [] },
    ])
    expect(ca!.node.get('a')).toBe(cb!.node.get('x'))
    expect(ca!.node.get('p')).toBe(cb!.node.get('y'))
    expect(ca!.wire.get('h')).toBe(cb!.wire.get('z'))
    expect(ca!.wire.get('v')).toBe(cb!.wire.get('w'))
    // Distinct content gets distinct colors.
    expect(ca!.node.get('a')).not.toBe(ca!.node.get('p'))
    expect(ca!.wire.get('h')).not.toBe(ca!.wire.get('v'))
  })

  it('refines by neighborhood: two pins differing only via their wires split', () => {
    const a = atomGraph({ atom: 'a', pin: 'p', head: 'h', value: 'v', valuePin: 'q' })
    const [ca] = refineJointly([{ diagram: a, pins: [] }])
    // Both are identity nodes, but one holds a rel1 wire, the other an iota wire.
    expect(ca!.node.get('p')).not.toBe(ca!.node.get('q'))
  })

  it('marks individualize: a marked element leaves its class', () => {
    // Two interchangeable pins on one arity-2 identity's wires.
    const d = mkDiagram({
      root: 'root',
      regions: { root: { kind: 'sheet' } },
      nodes: {
        j: { kind: 'identity', region: 'root', sig: IOTA, arity: 2 },
        p0: { kind: 'identity', region: 'root', sig: IOTA, arity: 1 },
        p1: { kind: 'identity', region: 'root', sig: IOTA, arity: 1 },
      },
      wires: {
        w0: { sig: IOTA, endpoints: [
          { node: 'j', port: { kind: 'identity', index: 0 } },
          { node: 'p0', port: { kind: 'identity', index: 0 } },
        ] },
        w1: { sig: IOTA, endpoints: [
          { node: 'j', port: { kind: 'identity', index: 1 } },
          { node: 'p1', port: { kind: 'identity', index: 0 } },
        ] },
      },
    })
    const [plain] = refineJointly([{ diagram: d, pins: [] }])
    expect(plain!.wire.get('w0')).toBe(plain!.wire.get('w1'))
    const [marked] = refineJointly(
      [{ diagram: d, pins: [] }],
      [{ side: 0, sort: 'wire', id: 'w0', token: 0 }],
    )
    expect(marked!.wire.get('w0')).not.toBe(marked!.wire.get('w1'))
    // The split propagates to the pins.
    expect(marked!.node.get('p0')).not.toBe(marked!.node.get('p1'))
  })

  it('pins enter initial colors positionally', () => {
    const d = mkDiagram({
      root: 'root',
      regions: { root: { kind: 'sheet' } },
      nodes: {
        j: { kind: 'identity', region: 'root', sig: IOTA, arity: 2 },
      },
      wires: {
        w0: { sig: IOTA, endpoints: [{ node: 'j', port: { kind: 'identity', index: 0 } }] },
        w1: { sig: IOTA, endpoints: [{ node: 'j', port: { kind: 'identity', index: 1 } }] },
      },
    })
    const [c] = refineJointly([{ diagram: d, pins: ['w0', 'w1'] }])
    expect(c!.wire.get('w0')).not.toBe(c!.wire.get('w1'))
  })

  it('throws on an unknown pinned wire', () => {
    const a = atomGraph({ atom: 'a', pin: 'p', head: 'h', value: 'v', valuePin: 'q' })
    expect(() => refineJointly([{ diagram: a, pins: ['nope'] }])).toThrow(/nope/)
  })
})
```

- [ ] **Step 2: Run test to verify it fails**

Run: `npx vitest run tests/kernel/diagram/refine.test.ts --config vitest.config.ts`
Expected: FAIL — cannot resolve `../../../src/kernel/diagram/canonical/refine`.

- [ ] **Step 3: Implement `refine.ts`**

Port the private machinery of `src/kernel/diagram/canonical/explore.ts` (do NOT modify explore.ts in this task — it stays working until Task 6 deletes it), generalized to N sides. Reference implementation (the tests are authoritative):

```ts
import type { Diagram, DiagramNode, NodeId, Port, RegionId, WireId } from '../diagram'
import { DiagramError } from '../diagram'
import { sigKey } from '../sig'

export type Sort = 'region' | 'node' | 'wire'

/** One individualization: element `id` of `sides[side]` gets token `token`
 *  folded into its initial color. Two marks with equal tokens pair the
 *  marked elements across sides. */
export type Mark = {
  readonly side: number
  readonly sort: Sort
  readonly id: string
  readonly token: number
}

export type RefinementSide = {
  readonly diagram: Diagram
  readonly pins: readonly WireId[]
}

export type SideColors = {
  readonly region: ReadonlyMap<RegionId, number>
  readonly node: ReadonlyMap<NodeId, number>
  readonly wire: ReadonlyMap<WireId, number>
}

export type RefineIndex = {
  readonly regionIds: readonly RegionId[]
  readonly nodeIds: readonly NodeId[]
  readonly wireIds: readonly WireId[]
  readonly regionKindKey: ReadonlyMap<RegionId, string>
  readonly parentOf: ReadonlyMap<RegionId, RegionId | null>
  readonly childrenOf: ReadonlyMap<RegionId, readonly RegionId[]>
  readonly nodesIn: ReadonlyMap<RegionId, readonly NodeId[]>
  readonly nodeContentKey: ReadonlyMap<NodeId, string>
  readonly nodeRegion: ReadonlyMap<NodeId, RegionId>
  readonly nodePortOrder: ReadonlyMap<NodeId, readonly string[]>
  readonly nodePortWire: ReadonlyMap<NodeId, ReadonlyMap<string, WireId>>
  readonly identityIncidentWires: ReadonlyMap<NodeId, readonly WireId[]>
  readonly wireSigKey: ReadonlyMap<WireId, string>
  readonly wireEndpoints: ReadonlyMap<WireId, readonly { node: NodeId; pkey: string }[]>
  readonly pinOf: ReadonlyMap<WireId, readonly number[]>
}

export function buildRefineIndex(d: Diagram, pins: readonly WireId[]): RefineIndex {
  // Verbatim port of buildExploreIndex (explore.ts:110–199), including
  // endpointKey (explore.ts:94–108), plus the pinned-wire existence check
  // from exploreLabeling (explore.ts:61–63): unknown pin -> DiagramError.
}

export function refineJointly(
  sides: readonly RefinementSide[],
  marks: readonly Mark[] = [],
): SideColors[] {
  const indexes = sides.map((s) => buildRefineIndex(s.diagram, s.pins))
  // Entries are keyed `${sideIndex}|R${id}` / `|N${id}` / `|W${id}` but the
  // SIGNATURE STRINGS NEVER CONTAIN THE SIDE INDEX — colors must be
  // comparable across sides.
  // Initial signatures (port of initialColors, explore.ts:219–233):
  //   region: `R|${kind}`
  //   node:   `N|${contentKey}`
  //   wire:   `W|${pins === undefined ? 'w' : 'pins' + JSON.stringify(pins)}`
  // then for each mark: append `|#${token}` to that element's initial
  // signature (sorted by token when several marks hit one element).
  // Rank all initial signatures jointly (port of rankSignatures,
  // explore.ts:211–217) -> numeric colors.
  // Refinement round (port of refineOnce, explore.ts:235–273), computed per
  // side with that side's index but ranked jointly across all entries.
  // Iterate while the joint class count grows (port of refine,
  // explore.ts:275–285). Return one SideColors per side.
}
```

The token suffix on *initial* signatures (rather than a color overwrite mid-refinement) is what makes restart-from-initial refinement equivalent to incremental individualization-refinement: marks only ever split classes.

- [ ] **Step 4: Run test to verify it passes**

Run: `npx vitest run tests/kernel/diagram/refine.test.ts --config vitest.config.ts`
Expected: PASS (5 tests).

- [ ] **Step 5: Typecheck and full suite**

Run: `npm run typecheck && npm test`
Expected: green (nothing consumes refine.ts yet; the suite guards against accidental edits elsewhere).

- [ ] **Step 6: Commit**

```bash
git add src/kernel/diagram/canonical/refine.ts tests/kernel/diagram/refine.test.ts
git commit -m "feat: joint color-refinement engine over one or two diagrams"
```

---

### Task 2: Pairwise isomorphism with verified witness

**Files:**
- Create: `src/kernel/diagram/canonical/iso.ts`
- Test: `tests/kernel/diagram/iso.test.ts`

**Interfaces:**
- Consumes: `refineJointly`, `Mark`, `Sort`, `SideColors` from `./refine`; `sigEquals` from `../sig`; `Diagram`, `DiagramError` from `../diagram`.
- Produces:
  - `type DiagramIso = { readonly regions: ReadonlyMap<RegionId, RegionId>; readonly nodes: ReadonlyMap<NodeId, NodeId>; readonly wires: ReadonlyMap<WireId, WireId> }` (moves here from explore.ts; Task 6 deletes the old one)
  - `diagramIso(a: Diagram, b: Diagram, aPins?: readonly WireId[], bPins?: readonly WireId[]): DiagramIso | null`
  - `sameDiagram(a: Diagram, b: Diagram, aPins?: readonly WireId[], bPins?: readonly WireId[]): boolean`
  - `__isoCounters: { individualizations: number; failedCandidates: number }` (production-neutral instrumentation, same convention as match.ts `__benchCounter`)

- [ ] **Step 1: Write the failing test**

```ts
// tests/kernel/diagram/iso.test.ts
import { describe, expect, it } from 'vitest'
import type { DiagramNode, Wire } from '../../../src/kernel/diagram/diagram'
import { mkDiagram } from '../../../src/kernel/diagram/diagram'
import {
  __isoCounters,
  diagramIso,
  sameDiagram,
} from '../../../src/kernel/diagram/canonical/iso'
import { IOTA, relSig } from '../../../src/kernel/diagram/sig'

/**
 * Disjoint rings of arity-2 identity nodes joined pairwise by wires.
 * rings([6]) asserts w1=…=w6; rings([3,3]) asserts two groups of three.
 * All nodes and wires are refinement-indistinguishable across the two.
 */
function rings(sizes: readonly number[]): ReturnType<typeof mkDiagram> {
  const nodes: Record<string, DiagramNode> = {}
  const wires: Record<string, Wire> = {}
  sizes.forEach((size, r) => {
    for (let i = 0; i < size; i++) {
      nodes[`id${r}_${i}`] = { kind: 'identity', region: 'root', sig: IOTA, arity: 2 }
    }
    for (let i = 0; i < size; i++) {
      wires[`w${r}_${i}`] = {
        sig: IOTA,
        endpoints: [
          { node: `id${r}_${i}`, port: { kind: 'identity', index: 1 } },
          { node: `id${r}_${(i + 1) % size}`, port: { kind: 'identity', index: 0 } },
        ],
      }
    }
  })
  return mkDiagram({ root: 'root', regions: { root: { kind: 'sheet' } }, nodes, wires })
}

/** rings() plus one hub identity wired to every ring node — connected variant. */
function hubbedRings(sizes: readonly number[]): ReturnType<typeof mkDiagram> {
  const total = sizes.reduce((s, x) => s + x, 0)
  const nodes: Record<string, DiagramNode> = {
    hub: { kind: 'identity', region: 'root', sig: IOTA, arity: total },
  }
  const wires: Record<string, Wire> = {}
  let spoke = 0
  sizes.forEach((size, r) => {
    for (let i = 0; i < size; i++) {
      nodes[`id${r}_${i}`] = { kind: 'identity', region: 'root', sig: IOTA, arity: 3 }
    }
    for (let i = 0; i < size; i++) {
      wires[`w${r}_${i}`] = {
        sig: IOTA,
        endpoints: [
          { node: `id${r}_${i}`, port: { kind: 'identity', index: 1 } },
          { node: `id${r}_${(i + 1) % size}`, port: { kind: 'identity', index: 0 } },
        ],
      }
      wires[`h${r}_${i}`] = {
        sig: IOTA,
        endpoints: [
          { node: `id${r}_${i}`, port: { kind: 'identity', index: 2 } },
          { node: 'hub', port: { kind: 'identity', index: spoke++ } },
        ],
      }
    }
  })
  return mkDiagram({ root: 'root', regions: { root: { kind: 'sheet' } }, nodes, wires })
}

const rel1 = relSig([IOTA])

describe('pairwise diagram isomorphism', () => {
  it('SOUNDNESS: one six-ring is not two three-rings (refinement-blind pair)', () => {
    expect(sameDiagram(rings([6]), rings([3, 3]))).toBe(false)
    expect(sameDiagram(rings([3, 3]), rings([6]))).toBe(false)
  })

  it('SOUNDNESS: hub-connected variant is also distinguished', () => {
    expect(sameDiagram(hubbedRings([6]), hubbedRings([3, 3]))).toBe(false)
  })

  it('finds and verifies an iso between equal symmetric structures', () => {
    const iso = diagramIso(rings([3, 3]), rings([3, 3]))
    expect(iso).not.toBeNull()
    expect(iso!.nodes.size).toBe(6)
    expect(iso!.wires.size).toBe(6)
  })

  it('DORMANCY: orbit-clean symmetric diagrams need zero failed candidates', () => {
    __isoCounters.failedCandidates = 0
    expect(diagramIso(rings([3, 3]), rings([3, 3]))).not.toBeNull()
    expect(diagramIso(rings([5]), rings([5]))).not.toBeNull()
    expect(__isoCounters.failedCandidates).toBe(0)
  })

  it('respects pinned boundary order, including refusing a swap', () => {
    const d = mkDiagram({
      root: 'root',
      regions: { root: { kind: 'sheet' } },
      nodes: {
        a: { kind: 'atom', region: 'root', sig: relSig([IOTA, IOTA]) },
        pin: { kind: 'identity', region: 'root', sig: relSig([IOTA, IOTA]), arity: 1 },
      },
      wires: {
        head: { sig: relSig([IOTA, IOTA]), endpoints: [
          { node: 'a', port: { kind: 'head' } },
          { node: 'pin', port: { kind: 'identity', index: 0 } },
        ] },
        x: { sig: IOTA, endpoints: [{ node: 'a', port: { kind: 'arg', index: 0 } }] },
        y: { sig: IOTA, endpoints: [{ node: 'a', port: { kind: 'arg', index: 1 } }] },
      },
    })
    // x and y are boundary-exposed (their boundary entry is their second end);
    // mkDiagram alone would reject them, so build via pins in the calls below.
    expect(sameDiagram(d, d, ['x', 'y'], ['x', 'y'])).toBe(true)
    expect(sameDiagram(d, d, ['x', 'y'], ['y', 'x'])).toBe(false)
    const iso = diagramIso(d, d, ['x', 'y'], ['x', 'y'])
    expect(iso!.wires.get('x')).toBe('x')
    expect(iso!.wires.get('y')).toBe('y')
  })

  it('is id-invariant: a wholesale renaming is recovered', () => {
    const make = (p: string) => mkDiagram({
      root: `${p}root`,
      regions: {
        [`${p}root`]: { kind: 'sheet' },
        [`${p}cut`]: { kind: 'cut', parent: `${p}root` },
      },
      nodes: {
        [`${p}atom`]: { kind: 'atom', region: `${p}cut`, sig: rel1 },
        [`${p}ref`]: { kind: 'ref', region: `${p}root`, defId: 'P', sig: rel1 },
        [`${p}hpin`]: { kind: 'identity', region: `${p}root`, sig: rel1, arity: 1 },
      },
      wires: {
        [`${p}head`]: { sig: rel1, endpoints: [
          { node: `${p}atom`, port: { kind: 'head' } },
          { node: `${p}hpin`, port: { kind: 'identity', index: 0 } },
        ] },
        [`${p}val`]: { sig: IOTA, endpoints: [
          { node: `${p}ref`, port: { kind: 'arg', index: 0 } },
          { node: `${p}atom`, port: { kind: 'arg', index: 0 } },
        ] },
      },
    })
    const iso = diagramIso(make('L'), make('R'))
    expect(iso).not.toBeNull()
    expect(iso!.regions.get('Lroot')).toBe('Rroot')
    expect(iso!.regions.get('Lcut')).toBe('Rcut')
    expect(iso!.nodes.get('Latom')).toBe('Ratom')
    expect(iso!.wires.get('Lval')).toBe('Rval')
  })

  it('rejects on plain census differences immediately', () => {
    expect(sameDiagram(rings([3]), rings([4]))).toBe(false)
    expect(sameDiagram(rings([3]), rings([3, 3]))).toBe(false)
  })

  it('rejects when pin arities differ', () => {
    const a = rings([3])
    expect(sameDiagram(a, a, ['w0_0'], [])).toBe(false)
  })
})
```

Note on the pin test: `mkDiagram` validates the two-end floor WITHOUT boundary; wires `x`/`y` above have one endpoint each, so `mkDiagram` would throw. Build that fixture with `validateRawDiagram(raw, ['x', 'y'])` instead (import from `../../../src/kernel/diagram/diagram`), which counts boundary entries as ends — mirror how `boundary.ts` `mkDiagramWithBoundary` constructs open diagrams. Adjust the fixture accordingly when writing the test file.

- [ ] **Step 2: Run test to verify it fails**

Run: `npx vitest run tests/kernel/diagram/iso.test.ts --config vitest.config.ts`
Expected: FAIL — cannot resolve `../../../src/kernel/diagram/canonical/iso`.

- [ ] **Step 3: Implement `iso.ts`**

```ts
import type { Diagram, NodeId, RegionId, WireId } from '../diagram'
import { DiagramError } from '../diagram'
import { sigEquals } from '../sig'
import { refineJointly, type Mark, type Sort } from './refine'

export type DiagramIso = {
  readonly regions: ReadonlyMap<RegionId, RegionId>
  readonly nodes: ReadonlyMap<NodeId, NodeId>
  readonly wires: ReadonlyMap<WireId, WireId>
}

/** Production-neutral counters; tests assert backstop dormancy through them. */
export const __isoCounters = { individualizations: 0, failedCandidates: 0 }

export function sameDiagram(
  a: Diagram, b: Diagram,
  aPins: readonly WireId[] = [], bPins: readonly WireId[] = [],
): boolean {
  return diagramIso(a, b, aPins, bPins) !== null
}

export function diagramIso(
  a: Diagram, b: Diagram,
  aPins: readonly WireId[] = [], bPins: readonly WireId[] = [],
): DiagramIso | null {
  if (aPins.length !== bPins.length) return null
  return attempt([])

  function attempt(marks: readonly Mark[]): DiagramIso | null {
    const [ca, cb] = refineJointly(
      [{ diagram: a, pins: aPins }, { diagram: b, pins: bPins }],
      marks,
    )
    // Group members by (sort, color) across the two sides.
    type Group = { sort: Sort; color: number; aMembers: string[]; bMembers: string[] }
    // ... build groups from ca!/cb! maps; if any group's aMembers.length !==
    // bMembers.length -> return null (covers all census mismatches).
    // If every group is a singleton pair -> build the three maps by color,
    // then verify (below); on verification failure THROW DiagramError —
    // discrete + stable + census-matched provably transports structure, so a
    // failure here is an engine bug, never a "not isomorphic".
    // Otherwise: tied = the group with aMembers.length > 1 having the
    // smallest color (deterministic). Fix aFixed = tied.aMembers.sort()[0].
    // For each bCand of tied.bMembers.sort():
    //   __isoCounters.individualizations++
    //   const r = attempt([...marks,
    //     { side: 0, sort: tied.sort, id: aFixed, token: marks.length / 2 },
    //     { side: 1, sort: tied.sort, id: bCand,  token: marks.length / 2 }])
    //   if (r !== null) return r
    //   __isoCounters.failedCandidates++
    // return null
  }
}

/** Linear structural transport check; returns a reason or null. */
function verifyIso(
  a: Diagram, b: Diagram,
  aPins: readonly WireId[], bPins: readonly WireId[],
  iso: DiagramIso,
): string | null {
  // 1. Bijectivity per sort: map sizes equal domain sizes; image sets equal
  //    codomain key sets.
  // 2. Regions: kind equal; parent of image === image of parent (sheet has none).
  // 3. Nodes: kind equal; region transports; atom: sigEquals; ref: defId equal
  //    + sigEquals; identity: sigEquals + arity equal.
  // 4. Wires: sigEquals; endpoint multiset transports — map each endpoint of
  //    the A-wire to `${iso.nodes.get(node)}|${positionKey}` (positionKey:
  //    'hd' | 'a:<i>' | 'i' — identity indices erased, same rule as
  //    occurrence-certificate.ts endpointPositionKey), sort, and compare with
  //    the B-wire's own sorted list.
  // 5. Pins: for each i, iso.wires.get(aPins[i]) === bPins[i].
}
```

Why the candidate choice is complete: colors are computed from content only, so any isomorphism maps `aFixed` to SOME member of the same class on the B side; all are tried. Why it terminates: each recursion level adds a token pair, which forces the marked elements into fresh singleton classes, so the joint class count strictly grows and depth is bounded by the element count.

- [ ] **Step 4: Run test to verify it passes**

Run: `npx vitest run tests/kernel/diagram/iso.test.ts --config vitest.config.ts`
Expected: PASS (8 tests). The two SOUNDNESS tests are this plan's reason to exist — if either fails, stop and debug; do not weaken them.

- [ ] **Step 5: Typecheck and full suite**

Run: `npm run typecheck && npm test`
Expected: green.

- [ ] **Step 6: Commit**

```bash
git add src/kernel/diagram/canonical/iso.ts tests/kernel/diagram/iso.test.ts
git commit -m "feat: pairwise refinement isomorphism with verified witness and dormant backstop"
```

---

### Task 3: Canonical wire order for definitions

**Files:**
- Create: `src/kernel/diagram/canonical/wire-order.ts`
- Modify: `src/app/define.ts:6-7,70`
- Test: `tests/kernel/diagram/wire-order.test.ts`

**Interfaces:**
- Consumes: `refineJointly`, `buildRefineIndex`, `Mark` from `./refine`.
- Produces: `canonicalWireOrder(d: Diagram): Map<WireId, number>` — the discrete canonical labeling's wire ordinals; equal-ordinal wires correspond across isomorphic diagrams. `define.ts` replaces `exploreLabeling(pattern.diagram).wireOrd` with `canonicalWireOrder(pattern.diagram)`.

- [ ] **Step 1: Write the failing test**

```ts
// tests/kernel/diagram/wire-order.test.ts
import { describe, expect, it } from 'vitest'
import { mkDiagram } from '../../../src/kernel/diagram/diagram'
import { canonicalWireOrder } from '../../../src/kernel/diagram/canonical/wire-order'
import { IOTA, relSig } from '../../../src/kernel/diagram/sig'

const rel1 = relSig([IOTA])

function graph(ids: { atom: string; hpin: string; head: string; val: string; vpin: string }) {
  return mkDiagram({
    root: 'root',
    regions: { root: { kind: 'sheet' } },
    nodes: {
      [ids.atom]: { kind: 'atom', region: 'root', sig: rel1 },
      [ids.hpin]: { kind: 'identity', region: 'root', sig: rel1, arity: 1 },
      [ids.vpin]: { kind: 'identity', region: 'root', sig: IOTA, arity: 1 },
    },
    wires: {
      [ids.head]: { sig: rel1, endpoints: [
        { node: ids.atom, port: { kind: 'head' } },
        { node: ids.hpin, port: { kind: 'identity', index: 0 } },
      ] },
      [ids.val]: { sig: IOTA, endpoints: [
        { node: ids.atom, port: { kind: 'arg', index: 0 } },
        { node: ids.vpin, port: { kind: 'identity', index: 0 } },
      ] },
    },
  })
}

describe('canonical wire order', () => {
  it('assigns each wire a distinct ordinal in 0..n-1', () => {
    const ord = canonicalWireOrder(graph({ atom: 'a', hpin: 'p', head: 'h', val: 'v', vpin: 'q' }))
    expect([...ord.values()].sort()).toEqual([0, 1])
  })

  it('is id-invariant: corresponding wires get equal ordinals', () => {
    const o1 = canonicalWireOrder(graph({ atom: 'a', hpin: 'p', head: 'h', val: 'v', vpin: 'q' }))
    const o2 = canonicalWireOrder(graph({ atom: 'z9', hpin: 'k', head: 'hd', val: 'w0', vpin: 'm' }))
    expect(o1.get('h')).toBe(o2.get('hd'))
    expect(o1.get('v')).toBe(o2.get('w0'))
  })

  it('breaks genuine symmetry deterministically (both orders occur, fixed)', () => {
    const symmetric = (w0: string, w1: string) => mkDiagram({
      root: 'root',
      regions: { root: { kind: 'sheet' } },
      nodes: {
        j: { kind: 'identity', region: 'root', sig: IOTA, arity: 2 },
        p0: { kind: 'identity', region: 'root', sig: IOTA, arity: 1 },
        p1: { kind: 'identity', region: 'root', sig: IOTA, arity: 1 },
      },
      wires: {
        [w0]: { sig: IOTA, endpoints: [
          { node: 'j', port: { kind: 'identity', index: 0 } },
          { node: 'p0', port: { kind: 'identity', index: 0 } },
        ] },
        [w1]: { sig: IOTA, endpoints: [
          { node: 'j', port: { kind: 'identity', index: 1 } },
          { node: 'p1', port: { kind: 'identity', index: 0 } },
        ] },
      },
    })
    const oa = canonicalWireOrder(symmetric('x', 'y'))
    const ob = canonicalWireOrder(symmetric('y', 'x'))
    // Interchangeable wires: the ordinals are a permutation of 0..1 either
    // way, and the function is a function of the diagram alone.
    expect([...oa.values()].sort()).toEqual([0, 1])
    expect([...ob.values()].sort()).toEqual([0, 1])
  })
})
```

- [ ] **Step 2: Run test to verify it fails**

Run: `npx vitest run tests/kernel/diagram/wire-order.test.ts --config vitest.config.ts`
Expected: FAIL — module not found.

- [ ] **Step 3: Implement `wire-order.ts`**

Port of explore.ts's lex-min search restricted to one side and returning only the wire ordinals. Structure:

```ts
import type { Diagram, WireId } from '../diagram'
import { buildRefineIndex, refineJointly, type Mark, type RefineIndex, type SideColors } from './refine'

/**
 * Discrete canonical wire ordinals — the definition-argument order.
 * Individualization-refinement with lex-min serialization: a class
 * refinement cannot split is an automorphism orbit ONLY when every member
 * is explored, so this search tries each and keeps the least form. Cold
 * path (once per definition, small bodies) — no orbit pruning by design
 * (spec §5, §9).
 */
export function canonicalWireOrder(d: Diagram): Map<WireId, number> {
  const idx = buildRefineIndex(d, [])
  const best = search([])
  return ordinalizeWires(idx, best.colors)

  function search(marks: readonly Mark[]): { form: string; colors: SideColors } {
    const [colors] = refineJointly([{ diagram: d, pins: [] }], marks)
    // firstTiedClass: port of explore.ts:288–315 over the single SideColors.
    // If none: return { form: serialize(idx, colors!), colors: colors! }.
    // Else recurse per member with an added mark { side: 0, sort, id,
    // token: marks.length } and keep the lexicographically least form.
  }
}
// serialize: port of serializeWith (explore.ts:339–359) using ordinals from
// the colors (port ordinalize/sortByOrd, explore.ts:361–368).
// ordinalizeWires: ordinalize(idx.wireIds, colors.wire).
```

- [ ] **Step 4: Run tests to verify they pass**

Run: `npx vitest run tests/kernel/diagram/wire-order.test.ts --config vitest.config.ts`
Expected: PASS (3 tests).

- [ ] **Step 5: Switch `define.ts`**

In `src/app/define.ts`: replace the import `import { exploreLabeling } from '../kernel/diagram/canonical/explore'` with `import { canonicalWireOrder } from '../kernel/diagram/canonical/wire-order'`, and line 70 `const ord = exploreLabeling(pattern.diagram).wireOrd` with `const ord = canonicalWireOrder(pattern.diagram)`.

- [ ] **Step 6: Typecheck and full suite**

Run: `npm run typecheck && npm test`
Expected: green — `canonicalArgOrder`'s behavior is unchanged (same algorithm, same tie-breaking by id sort), so define/fold tests must pass as-is. If any define-related test changes verdict, the port has a bug (most likely: tie order in the tied-class member loop, or serialization drift); fix the port, do not touch the tests.

- [ ] **Step 7: Commit**

```bash
git add src/kernel/diagram/canonical/wire-order.ts tests/kernel/diagram/wire-order.test.ts src/app/define.ts
git commit -m "feat: canonical wire order module; define.ts drops exploreLabeling"
```

---

### Task 4: Kernel call sites move to pairwise iso

**Files:**
- Modify: `src/kernel/proof/theorem.ts:11,110-113,184,242`
- Modify: `src/kernel/rules/fold.ts:18,221-226`
- Modify: `src/kernel/proof/compose.ts:3,330,408`
- Modify: `src/kernel/proof/compile-content.ts:13,935,965,1080-1085,1095-1100`
- Modify: `src/kernel/rules/iteration.ts:5,148,167-174`

No new tests: these are behavior-preserving conversions (string-equality of canonical forms ⇔ `sameDiagram`; `exploreIso` ⇔ `diagramIso`), and each site is already covered by the kernel proof/rules suites. The full suite is the gate.

- [ ] **Step 1: `theorem.ts`**

- Import: replace `import { exploreForm } from '../diagram/canonical/explore'` with `import { sameDiagram } from '../diagram/canonical/iso'` and add `import { diagramToJson } from '../diagram/json'` (check the existing import block — json helpers may already be imported).
- Line 110–113:

```ts
if (!sameDiagram(fwd, bwd, fwdInterface.boundary(), bwdInterface.boundary())) {
  const detail = process.env.THEOREM_DEBUG
    ? `\n-- forward:\n${JSON.stringify(diagramToJson(fwd))}\n-- stated/backward:\n${JSON.stringify(diagramToJson(bwd))}`
    : ''
```

- Line 242: `if (!sameDiagram(candidate.diagram, from.diagram, candidate.boundary, from.boundary)) {`
- Line 184: the comment mentions `exploreForm`; reword it to reference the boundary-pinned isomorphism check (`sameDiagram`).

- [ ] **Step 2: `fold.ts`**

Replace the import and lines 221–226:

```ts
if (!sameDiagram(
  extracted.pattern.diagram, expected.pattern.diagram,
  actualPins, expectedPins,
)) {
  throw new RuleError(
    'fold: the occurrence does not match the definition under its pinned boundary',
  )
}
```

(The old message said "canonical forms differ" — no canonical forms exist anymore; the reworded message states the actual check.)

- [ ] **Step 3: `compose.ts`**

Replace `import { exploreIso } from '../diagram/canonical/explore'` with `import { diagramIso } from '../diagram/canonical/iso'`; both call sites (line 330, line 408) rename `exploreIso(` → `diagramIso(` — argument lists unchanged. The `DiagramIso` type import, if present, moves to `../diagram/canonical/iso`.

- [ ] **Step 4: `compile-content.ts`**

- Import `sameDiagram, diagramIso` from `../diagram/canonical/iso`, `diagramToJson` from `../diagram/json`; drop the explore import.
- Line 935: delete `const firstForm = exploreForm(...)`.
- Line 965 area: replace the form comparison with

```ts
if (!sameDiagram(
  candidate.pattern.diagram, first.pattern.diagram,
  candidate.pattern.boundary, first.pattern.boundary,
)) {
```

- Lines 1080–1085 and 1095–1100: `exploreIso(` → `diagramIso(`; in both error messages replace each `exploreForm(X)` interpolation with `JSON.stringify(diagramToJson(X))`.

- [ ] **Step 5: `iteration.ts`**

- Import `diagramIso` from `../diagram/canonical/iso`; drop `exploreForm, exploreIso`.
- Delete line 148 (`const want = exploreForm(...)`) and the line-167 form prefilter (`if (exploreForm(probe...) !== want) continue`). The existing attachment-list equality checks above it stay — they are the cheap prefilter. The `exploreIso` call becomes `diagramIso` with the same arguments; its `null` check already `continue`s, which now absorbs the deleted prefilter's job.

- [ ] **Step 6: Typecheck and full suite**

Run: `npm run typecheck && npm test`
Expected: green. These suites (theorem, fold, compose, compile-content, iteration, frege theories) are the behavioral gate for this task.

- [ ] **Step 7: Commit**

```bash
git add src/kernel/proof/theorem.ts src/kernel/rules/fold.ts src/kernel/proof/compose.ts src/kernel/proof/compile-content.ts src/kernel/rules/iteration.ts
git commit -m "refactor: kernel equality/iso checks use pairwise diagramIso"
```

---

### Task 5: App and theories call sites; dead fingerprint field deleted

**Files:**
- Modify: `src/app/session.ts:3,287-288`
- Modify: `src/app/replay.ts:3-4,105-106,132`
- Modify: `src/app/copy-planner.ts:40,167` (delete `resultFingerprint`)
- Modify: `src/app/shell.ts:6,1977-1982`
- Modify: `e2e/interaction.spec.ts:32,215,220-225` (rename hook)
- Modify: `src/theories/reification.ts:8,133-148,156-160`

- [ ] **Step 1: `session.ts`**

Import `sameDiagram` from `../kernel/diagram/canonical/iso`; `meet()` becomes:

```ts
export function meet(s: ProofSession): boolean {
  assertSession(s)
  return sameDiagram(
    currentSide(s, 'forward'), currentSide(s, 'backward'),
    sideBoundary(s, 'forward'), sideBoundary(s, 'backward'),
  )
}
```

- [ ] **Step 2: `replay.ts`**

Import `diagramIso, sameDiagram` (and keep the `DiagramIso` type import, now from `../kernel/diagram/canonical/iso`). Line 105–106 becomes `if (!sameDiagram(forwardMeet, backwardMeet, forwardMeetBoundary, backwardMeetBoundary)) {`. Line 132 `exploreIso(` → `diagramIso(`.

- [ ] **Step 3: `copy-planner.ts` — delete the dead field**

`resultFingerprint` is written at copy-planner.ts:167 and read NOWHERE (verified by repo grep across src and tests). Per no-dead-code policy, delete it: remove the field from the `CopyPlan` proof variant (line 40) and from the `finishPlan({ kind: 'proof', action, resultFingerprint: ... })` construction (line 167); drop the `exploreForm` import. If tsc then reveals a reader the grep missed, STOP deleting and convert that reader to hold the result `Diagram` and compare with `sameDiagram` instead — do not reintroduce a canonical-form string.

- [ ] **Step 4: `shell.ts` debug hook + e2e**

The e2e uses the hook to assert "defining a relation leaves the EDIT sheet untouched". Untouched means storage-identical, so strict JSON equality is the honest (and stronger) assertion — no isomorphism needed:

- shell.ts: drop the `exploreForm` import; ensure `diagramToJson` is imported from `../kernel/diagram/json`; replace the `editForm()` member (lines ~1977–1982) with:

```ts
// The EDIT sheet's storage as JSON — an e2e compares snapshots to assert
// defining a relation leaves the sheet untouched (the spec's "no diagram
// changes when a relation is defined").
editJson(): string {
  return JSON.stringify(diagramToJson(editDiagram))
},
```

- e2e/interaction.spec.ts: rename the declaration (line 32) `editForm(): string` → `editJson(): string` and the three call sites (lines ~215, ~225, and the later two `editForm()` evaluations) to `editJson()`.

- [ ] **Step 5: `reification.ts`**

Replace `selectedChildForm` (returns a canonical string) with an extractor returning the open diagram, and compare pairwise in `copiedChild`:

```ts
import { sameDiagram } from '../kernel/diagram/canonical/iso'

function selectedChild(
  diagram: Diagram,
  parent: RegionId,
  child: RegionId,
): DiagramWithBoundary {
  const extracted = extractSubgraph(diagram, {
    region: parent,
    regions: [child],
    nodes: [],
    wires: [],
  })
  return extracted.pattern
}

function copiedChild(
  diagram: Diagram,
  sourceParent: RegionId,
  sourceChild: RegionId,
  targetParent: RegionId,
): RegionId {
  const expected = selectedChild(diagram, sourceParent, sourceChild)
  return exactOne(
    directCuts(diagram, targetParent)
      .filter((candidate) => {
        const probe = selectedChild(diagram, targetParent, candidate)
        return sameDiagram(
          probe.diagram, expected.diagram,
          probe.boundary, expected.boundary,
        )
      }),
    'copied implication consequent',
  )
}
```

(`DiagramWithBoundary` import from `../kernel/diagram/boundary` if not present; drop the `exploreForm` import. This is semantics-preserving: the old code compared boundary-pinned canonical forms, which is exactly pin-respecting isomorphism.)

- [ ] **Step 6: Typecheck, full suite, e2e sanity**

Run: `npm run typecheck && npm test`
Expected: green.
Then run the affected e2e spec if the environment has browsers available: `npm run e2e -- e2e/interaction.spec.ts`. If the e2e environment is unavailable, say so explicitly in the task report (with the command that failed) — do not claim e2e verification.

- [ ] **Step 7: Commit**

```bash
git add src/app/session.ts src/app/replay.ts src/app/copy-planner.ts src/app/shell.ts e2e/interaction.spec.ts src/theories/reification.ts
git commit -m "refactor: app/theories equality checks use pairwise iso; drop dead resultFingerprint"
```

---

### Task 6: Convert canonical test files; delete explore.ts

**Files:**
- Modify: `tests/kernel/diagram/explore.test.ts`
- Modify: `tests/kernel/diagram/canonical.test.ts`
- Modify: `tests/kernel/diagram/canonical-ports.test.ts`
- Modify: `tests/kernel/diagram/canonical-adversarial.test.ts`
- Modify: `tests/kernel/diagram/labeling.test.ts`
- Modify: `src/kernel/diagram/index.ts:18`
- Delete: `src/kernel/diagram/canonical/explore.ts`

Each existing test asserts a behavioral claim (X and Y are/aren't structurally equal; corresponding elements correspond; wire order is deterministic). The claims are all preserved; only the API changes. Mechanical conversion rules — apply them test by test, reading each test to confirm which rule fits (do not regex-replace blindly):

| Old assertion | New assertion |
|---|---|
| `expect(exploreForm(a)).toBe(exploreForm(b))` | `expect(sameDiagram(a, b)).toBe(true)` |
| `expect(exploreForm(a)).not.toBe(exploreForm(b))` | `expect(sameDiagram(a, b)).toBe(false)` |
| `expect(exploreForm(a, pinsA)).toBe(exploreForm(b, pinsB))` | `expect(sameDiagram(a, b, pinsA, pinsB)).toBe(true)` (and `.not.toBe` ⇒ `false`) |
| `boundaryForm(dwb)` comparisons | `sameDiagram(x.diagram, y.diagram, x.boundary, y.boundary)` |
| `exploreIso(a, b, ...)` | `diagramIso(a, b, ...)` — mapping assertions unchanged where the mapping is forced (asymmetric diagrams); where a test asserted a specific mapping on a SYMMETRIC diagram, weaken only to "maps within the orbit" if the old expectation depended on lex-min tie-breaking that no longer exists. Flag any such weakening in the task report. |
| `exploreLabeling(d).wireOrd` (in labeling.test.ts) | `canonicalWireOrder(d)` for wire-order claims; for region/node ordinal claims with no remaining consumer, convert the claim to the equivalent `diagramIso` correspondence assertion (corresponding elements map to each other) |
| Form-string CONTENT assertions (a test inspecting the serialized string itself, if any exist) | The serialization is gone; convert to the structural claim the string stood for (equality/inequality/pin sensitivity via `sameDiagram`). Flag each in the task report. |

- [ ] **Step 1: Convert the five test files** per the table. Keep every `it(...)` title's claim intact (retitle only where a title names `exploreForm` itself).

- [ ] **Step 2: Run the converted files**

Run: `npx vitest run tests/kernel/diagram/explore.test.ts tests/kernel/diagram/canonical.test.ts tests/kernel/diagram/canonical-ports.test.ts tests/kernel/diagram/canonical-adversarial.test.ts tests/kernel/diagram/labeling.test.ts --config vitest.config.ts`
Expected: PASS. A converted test that fails is reporting a real behavioral difference between old and new engines — STOP and debug the engine (Tasks 1–3), never adjust the expectation to the new engine's answer.

- [ ] **Step 3: Delete `explore.ts` and fix the kernel index**

- Delete `src/kernel/diagram/canonical/explore.ts`.
- `src/kernel/diagram/index.ts:18`: replace `export { exploreForm, boundaryForm, exploreLabeling, exploreIso } from './canonical/explore'` with `export { diagramIso, sameDiagram } from './canonical/iso'` and `export type { DiagramIso } from './canonical/iso'`. (`canonicalWireOrder` is NOT exported from the index — its one consumer, `define.ts`, imports it directly.)
- Run `rg -n "canonical/explore|exploreForm|exploreIso|exploreLabeling|boundaryForm" src tests e2e` — expected: zero hits. Any hit is an unconverted consumer; convert it now.

- [ ] **Step 4: Typecheck and full suite**

Run: `npm run typecheck && npm test`
Expected: green.

- [ ] **Step 5: Commit**

```bash
git add tests/kernel/diagram/explore.test.ts tests/kernel/diagram/canonical.test.ts tests/kernel/diagram/canonical-ports.test.ts tests/kernel/diagram/canonical-adversarial.test.ts tests/kernel/diagram/labeling.test.ts src/kernel/diagram/index.ts
git rm src/kernel/diagram/canonical/explore.ts
git commit -m "refactor: canonical tests target pairwise iso; delete labeling-based explore"
```

---

### Task 7: Occurrence matcher rewrite — propagation core

**Files:**
- Modify: `src/kernel/diagram/subgraph/match.ts` (full engine replacement; public surface unchanged)
- Modify: `docs/superpowers/specs/2026-08-13-refinement-driven-iso-and-matching-design.md` §6 first bullet (the amendment in Global Constraints)
- Test: `tests/kernel/diagram/match-propagation.test.ts` (new; targets the exported engine seam described below)

**Interfaces:**
- Preserved public surface of `match.ts`: `findOccurrences(host, pattern, opts)`, `MatchResult`, `Occurrence` (= `OccurrenceCertificate`), `__benchCounter = { n: 0, permutations: 0 }` (`n` now counts candidate placement attempts; `permutations` counts recorded pre-dedupe assignments).
- Consumes: `buildRefineIndex` from `../canonical/refine` (for content keys, port wiring, incidences), `derivedScope, derivedScopes, isAncestorOrEqual` from `../regions`, `checkOccurrenceCertificate` from `./occurrence-certificate`, `sigKey/sigEquals` from `../sig`.

This task builds and unit-tests the candidate/propagation layer; Task 8 wires it into the search and the public function. To keep every commit green, Task 7 ADDS the new internals to `match.ts` (exported with the `__` test-seam convention) while `findOccurrences` still runs the old engine; Task 8 swaps the engine and deletes the old internals.

**The layer's contract (every filter must be a NECESSARY condition — implied by the existence of an occurrence extending the current state; anything stronger loses occurrences = kernel incompleteness):**

Candidate initialization (`__initCandidates(host, pattern, opts)` returning `{ region: Map<RegionId, Set<RegionId>>; node: Map<NodeId, Set<NodeId>>; wire: Map<WireId, Set<WireId>> } | null`):
- Pattern root region → `opts.inRegion` if given, else all host regions.
- Pattern cut → host cuts with equal subtree fingerprint. Fingerprint (computed bottom-up once per diagram): `` `cut(${sorted child fingerprints};${sorted node contentKeys directly in the region};${sorted sigKeys of wires scoped at the region})` `` — pattern scopes derived WITH the pattern boundary (`derivedScopes(patternDiagram, pattern.boundary)`), host scopes without. Boundary wires scope to the pattern root, so they never appear in a nested cut's fingerprint; the pattern ROOT's fingerprint is never used (the top container is at-least, not exact). This census-exactness is today's `matchSubtree` equality gate (match.ts:285-291) made into a one-shot invariant — the spec-§6 amendment names it as the "host colored once" invariant.
- Pattern node → host nodes with equal content key (`buildRefineIndex(...).nodeContentKey`: kind + sig, + defId for refs, + arity for identities — matching today's `nodeCompatible`).
- Internal pattern wire → host wires with equal `sigKey` AND equal endpoint count.
- Boundary pattern wire → the seeded attachment if `opts.attachments` is given (conflicting seeds for one repeated boundary wire ⇒ that wire's set is empty ⇒ `findOccurrences` returns zero matches, today's `seededCandidate` behavior); else host wires with equal `sigKey` and endpoint count ≥ the pattern wire's.
- Any empty initial set → `null` (no occurrences anywhere).

Propagation (`__propagate(ctx, candidates, dirtyIds)` — worklist to fixpoint; returns `false` if any set empties):
1. Cut/parent, both directions: cut c with pattern parent p: `C(c) ⊆ {h : hostParent(h) ∈ C(p)}` and `C(p) ⊆ {g : some h ∈ C(c) has hostParent(h) = g}`.
2. Node/region, both directions: node n in pattern region r: `C(n) ⊆ {h : hostRegion(h) ∈ C(r)}` and `C(r) ⊆ {g : some h ∈ C(n) has hostRegion(h) = g}`.
3. Positional ports, both directions: for atom/ref node n, port key pk, pattern wire w at that port: `C(n) ⊆ {h : hostPortWire(h, pk) ∈ C(w)}` and `C(w) ⊆ {hostPortWire(h, pk) : h ∈ C(n)}`. (Sound for boundary wires too: the image of ANY pattern wire incident at a positional port is forced to be the host wire at the image node's same port.)
4. Wire/endpoint support, both directions, all wires: for each pattern endpoint (n, pkey) of wire w: `C(w) ⊆ {hw : some host endpoint (m, pkey) of hw has m ∈ C(n)}` and `C(n) ⊆ {m : some hw ∈ C(w) has endpoint (m, pkey)}` — the second direction only for nodes ALL of whose incidences are to pattern wires (always true: every port of every pattern node is attached, validateRawDiagram guarantees it).
5. Internal-wire scope: internal wire w with pattern scope s (from `derivedScopes(pattern.diagram, pattern.boundary)`): `C(w) ⊆ {hw : hostScope(hw) ∈ C(s)}`. (Boundary-wire scope needs the chosen root — checked at root assignment in Task 8's search, `isAncestorOrEqual(host, hostScope(hw), hostRoot)`.)

Endpoint position keys reuse today's `endpointPositionKey` (match.ts:56-70): `'hd'`, `'a:<i>'`, `'i'` — identity indices erased.

- [ ] **Step 1: Write the failing tests**

```ts
// tests/kernel/diagram/match-propagation.test.ts
import { describe, expect, it } from 'vitest'
import { mkDiagramWithBoundary } from '../../../src/kernel/diagram/boundary'
import { mkDiagram } from '../../../src/kernel/diagram/diagram'
import { __initCandidates, __propagate, __makePropagationContext } from '../../../src/kernel/diagram/subgraph/match'
import { IOTA, relSig } from '../../../src/kernel/diagram/sig'

const rel2 = relSig([IOTA, IOTA])

/** Host: chain ref d0 -(w0)- ref d1 -(w1)- ref d2, ends pinned. Distinct defIds. */
function chainHost() {
  return mkDiagram({
    root: 'root',
    regions: { root: { kind: 'sheet' } },
    nodes: {
      r0: { kind: 'ref', region: 'root', defId: 'd0', sig: rel2 },
      r1: { kind: 'ref', region: 'root', defId: 'd1', sig: rel2 },
      r2: { kind: 'ref', region: 'root', defId: 'd2', sig: rel2 },
      pL: { kind: 'identity', region: 'root', sig: IOTA, arity: 1 },
      pR: { kind: 'identity', region: 'root', sig: IOTA, arity: 1 },
    },
    wires: {
      end0: { sig: IOTA, endpoints: [
        { node: 'r0', port: { kind: 'arg', index: 0 } },
        { node: 'pL', port: { kind: 'identity', index: 0 } },
      ] },
      w0: { sig: IOTA, endpoints: [
        { node: 'r0', port: { kind: 'arg', index: 1 } },
        { node: 'r1', port: { kind: 'arg', index: 0 } },
      ] },
      w1: { sig: IOTA, endpoints: [
        { node: 'r1', port: { kind: 'arg', index: 1 } },
        { node: 'r2', port: { kind: 'arg', index: 0 } },
      ] },
      end1: { sig: IOTA, endpoints: [
        { node: 'r2', port: { kind: 'arg', index: 1 } },
        { node: 'pR', port: { kind: 'identity', index: 0 } },
      ] },
    },
  })
}

/** Pattern: single ref d1 with both args boundary-exposed. */
function d1Pattern() {
  return mkDiagramWithBoundary(
    {
      root: 'proot',
      regions: { proot: { kind: 'sheet' } },
      nodes: { n: { kind: 'ref', region: 'proot', defId: 'd1', sig: rel2 } },
      wires: {
        a: { sig: IOTA, endpoints: [{ node: 'n', port: { kind: 'arg', index: 0 } }] },
        b: { sig: IOTA, endpoints: [{ node: 'n', port: { kind: 'arg', index: 1 } }] },
      },
    },
    ['a', 'b'],
  )
}

describe('matcher candidate propagation', () => {
  it('content filtering pins a distinct ref to its unique host image', () => {
    const host = chainHost()
    const pattern = d1Pattern()
    const ctx = __makePropagationContext(host, pattern, {})
    const cands = __initCandidates(ctx)
    expect(cands).not.toBeNull()
    expect([...cands!.node.get('n')!]).toEqual(['r1'])
  })

  it('positional-port propagation forces the boundary wire images', () => {
    const host = chainHost()
    const pattern = d1Pattern()
    const ctx = __makePropagationContext(host, pattern, {})
    const cands = __initCandidates(ctx)!
    const ok = __propagate(ctx, cands)
    expect(ok).toBe(true)
    expect([...cands.wire.get('a')!]).toEqual(['w0'])
    expect([...cands.wire.get('b')!]).toEqual(['w1'])
  })

  it('a contradictory seed empties a candidate set', () => {
    const host = chainHost()
    const pattern = d1Pattern()
    // Seed boundary position 0 (wire a) to end1 — but a must be r1's arg0
    // wire, which is w0. Init keeps the seed; propagation must fail.
    const ctx = __makePropagationContext(host, pattern, { attachments: ['end1', 'w1'] })
    const cands = __initCandidates(ctx)!
    expect(__propagate(ctx, cands)).toBe(false)
  })

  it('nested-cut fingerprints restrict cut candidates to census-equal cuts', () => {
    const host = mkDiagram({
      root: 'root',
      regions: {
        root: { kind: 'sheet' },
        empty: { kind: 'cut', parent: 'root' },
        full: { kind: 'cut', parent: 'root' },
      },
      nodes: { j: { kind: 'identity', region: 'full', sig: IOTA, arity: 0 } },
      wires: {},
    })
    const pattern = mkDiagramWithBoundary(
      {
        root: 'proot',
        regions: { proot: { kind: 'sheet' }, pcut: { kind: 'cut', parent: 'proot' } },
        nodes: {},
        wires: {},
      },
      [],
    )
    const ctx = __makePropagationContext(host, pattern, {})
    const cands = __initCandidates(ctx)!
    expect([...cands.region.get('pcut')!]).toEqual(['empty'])
  })
})
```

(Arity-0 identity nodes are legal — diagram.ts:16-21 — and need no wires, which keeps the fingerprint fixture minimal.)

- [ ] **Step 2: Run tests to verify they fail**

Run: `npx vitest run tests/kernel/diagram/match-propagation.test.ts --config vitest.config.ts`
Expected: FAIL — `__initCandidates` etc. are not exported.

- [ ] **Step 3: Implement the propagation layer in `match.ts`**

Add (old engine untouched and still serving `findOccurrences`):

```ts
export type PropagationContext = {
  readonly host: Diagram
  readonly pattern: DiagramWithBoundary
  readonly opts: { readonly inRegion?: RegionId; readonly attachments?: readonly WireId[] }
  readonly hostIdx: RefineIndex        // buildRefineIndex(host, [])
  readonly patternIdx: RefineIndex     // buildRefineIndex(pattern.diagram, pattern.boundary)
  readonly patternScopes: ReadonlyMap<WireId, RegionId>   // derivedScopes with boundary
  readonly hostScopes: ReadonlyMap<WireId, RegionId>      // derivedScopes without
  readonly hostFingerprint: ReadonlyMap<RegionId, string>
  readonly patternFingerprint: ReadonlyMap<RegionId, string>
  readonly boundarySet: ReadonlySet<WireId>
}
export function __makePropagationContext(host, pattern, opts): PropagationContext
export type CandidateSets = {
  readonly region: Map<RegionId, Set<RegionId>>
  readonly node: Map<NodeId, Set<NodeId>>
  readonly wire: Map<WireId, Set<WireId>>
}
export function __initCandidates(ctx: PropagationContext): CandidateSets | null
export function __propagate(ctx: PropagationContext, cands: CandidateSets): boolean
```

Implementation notes:
- Fingerprints bottom-up: process regions in decreasing depth (`cutDepth` from `../regions` or a local postorder); memoize in a Map.
- `__propagate` worklist: seed with every pattern element id; on shrinking any set, enqueue that element's constraint neighbors (its region's parent/children/nodes, its node's wires, its wire's endpoint nodes). Sets are mutated in place. Return `false` the moment any set empties.
- Determinism: iterate candidate sets in sorted order when materializing arrays (tests use `toEqual` on sorted expectations).
- Keep `__benchCounter` untouched in this task.

- [ ] **Step 4: Run tests to verify they pass**

Run: `npx vitest run tests/kernel/diagram/match-propagation.test.ts --config vitest.config.ts`
Expected: PASS (4 tests).

- [ ] **Step 5: Amend the spec sentence**

In `docs/superpowers/specs/2026-08-13-refinement-driven-iso-and-matching-design.md` §6, replace the bullet "Host is refined once (unseeded; colors are invariants of the host)." with:

```
- The host-side invariant computed once is the nested-cut subtree
  fingerprint (censuses of children, nodes, and scoped wires, recursively);
  whole-host refinement colors are not fragment-comparable — a
  boundary-adjacent pattern element's image color depends on host context
  outside the occurrence — so they are deliberately not used as filters.
```

- [ ] **Step 6: Typecheck and full suite**

Run: `npm run typecheck && npm test`
Expected: green (old engine still active; new layer is additive).

- [ ] **Step 7: Commit**

```bash
git add src/kernel/diagram/subgraph/match.ts tests/kernel/diagram/match-propagation.test.ts docs/superpowers/specs/2026-08-13-refinement-driven-iso-and-matching-design.md
git commit -m "feat: matcher candidate-set propagation layer (engine swap follows)"
```

---

### Task 8: Occurrence matcher rewrite — search engine swap

**Files:**
- Modify: `src/kernel/diagram/subgraph/match.ts` (replace the old engine's internals with the propagation-driven search)
- Modify: `tests/kernel/diagram/match-explore.test.ts` (counter-semantics conversion only)

**Interfaces:** `findOccurrences` signature, `MatchResult`, `Occurrence`, and all option validation behavior are IDENTICAL to today (match.ts:76-124: fuel validation, unknown `inRegion`, attachment count/existence checks, bare-boundary-wire-without-attachments error). The existing suites `match.test.ts`, `match-open.test.ts`, `match-roundtrip.test.ts`, `match-adversarial.test.ts`, plus every kernel/app consumer, are the gate and MUST pass without modification.

- [ ] **Step 1: Replace the engine**

Keep verbatim: the option-validation block, `endpointPositionKey`, the footprint-dedupe logic, `recordOccurrence`'s certificate check-and-throw, and the `Occurrence` construction shape (match.ts:440-467). Delete: `buildIndex`, `assignContainer`, `assignInjective`, `matchSubtree`, `assignWires`, `nodeCompatible`, `wireCompatible`, `identityIncidencesMatch`, `seededCandidate` (their jobs move into init/propagation/search as below).

New search:

```
findOccurrences(host, pattern, opts):
  validate options (verbatim block)
  ctx = __makePropagationContext(host, pattern, opts)
  cands0 = __initCandidates(ctx); if null -> { status: 'complete', matches: [], explorationSteps: 0 }
  if !__propagate(ctx, cands0) -> complete, no matches
  order: pattern root region FIRST, then on demand: unassigned element with the
    smallest candidate set (ties: region < node < wire, then id sort)
  state: regionMap/nodeMap/wireMap + usedRegions/usedNodes/usedInternalWires
    (boundary wires may alias each other; they only conflict with INTERNAL
    images — exactly today's assignWires rules, match.ts:387-391)
  assign(element, image):
    spend() one fuel unit (today's semantics: false -> exhausted, stop all)
    __benchCounter.n++
    injectivity check per the used-sets above; boundary-wire root-scope check
      when element is a boundary wire: isAncestorOrEqual(host,
      hostScope(image), regionMap(patternRoot))
    branch on a COPY of the candidate sets: set C(element) = {image},
      run __propagate restricted-start from element; dead -> unwind
    when a wire's full local context is assigned, run the EXACT residual
      checks relocated from the old engine (necessary-only propagation does
      not guarantee them):
      - internal wire fully assigned + all its endpoint nodes assigned:
        endpoint multiset equality (old wireCompatible non-boundary branch:
        mapped pattern endpoint keys sorted === host endpoint keys sorted)
      - boundary wire + its endpoint nodes: sub-multiset containment (old
        boundary branch)
      - identity node + all its incident pattern wires assigned: incident
        multiset EXACT equality against the host node's full incident list
        (old identityIncidencesMatch, relocated to fire as early as possible)
      failure -> unwind (dead branch), NOT an error
  all assigned -> recordOccurrence (footprint dedupe + certificate check
    which THROWS on failure — an invalid constructed certificate is an
    engine bug, same contract as today, match.ts:460-465)
  enumerate root candidates in sorted order (today's candidates loop,
    match.ts:149-163) so occurrence ORDER stays deterministic
```

`__benchCounter.n` counts placement attempts; `permutations` counts full assignments reaching `recordOccurrence` (pre-dedupe). Both are reset-and-read by tests only.

- [ ] **Step 2: Run the matcher suites**

Run: `npx vitest run tests/kernel/diagram/match.test.ts tests/kernel/diagram/match-open.test.ts tests/kernel/diagram/match-roundtrip.test.ts tests/kernel/diagram/match-adversarial.test.ts tests/kernel/diagram/match-propagation.test.ts --config vitest.config.ts`
Expected: PASS with NO test-file edits. Failures mean the new engine drops or invents occurrences — debug the engine (most likely: an over-strong propagation filter, a missing residual exact check, or fuel spend placement); never adjust these tests.

One systematic hazard to check when a test fails on `explorationSteps` or `status`: fuel is spent per placement attempt in BOTH engines, but the new engine attempts far fewer placements. A test asserting `status: 'exhausted'` under a small fuel may now complete. That is the intended improvement, and such a test is asserting the OLD engine's inefficiency, not the contract — this is the ONE exception to "never adjust": convert the assertion to the new engine's honest behavior (e.g., assert `complete` with the correct matches, or shrink fuel to still exhaust a genuinely large search). List every such conversion in the task report with old and new values.

- [ ] **Step 3: Convert `match-explore.test.ts`**

This file resets `__benchCounter.n` and asserts `n > 4` (old semantics: `nodeCompatible` calls). Read each assertion, keep the test's claim (the matcher does bounded exploration work and reports steps faithfully), and re-target the counters to the new semantics (placement attempts). Same STOP rule as Step 2 for any behavioral assertion.

- [ ] **Step 4: Typecheck and full suite**

Run: `npm run typecheck && npm test`
Expected: green — this is the whole-system gate for the engine swap (cite, define/inferFoldArgs, iteration, splice/extract roundtrips all exercise `findOccurrences`).

- [ ] **Step 5: Commit**

```bash
git add src/kernel/diagram/subgraph/match.ts tests/kernel/diagram/match-explore.test.ts
git commit -m "feat: occurrence matcher runs on propagation-driven search; factorial engine deleted"
```

---

### Task 9: Matcher efficiency tests and fuel budget review

**Files:**
- Modify: `tests/kernel/diagram/match-adversarial.test.ts` (append new describe block)
- Modify (as the audit dictates): `src/app/interact/cite.ts:70`, `src/app/define.ts:96-99`, `src/kernel/rules/iteration.ts:215-226` fuel budgets

- [ ] **Step 1: Write the failing efficiency tests**

Append to `tests/kernel/diagram/match-adversarial.test.ts`:

```ts
describe('propagation-driven matching does no blind search', () => {
  it('a rigid chain is matched in exactly one placement per element', () => {
    // Host: the 3-ref chain from match-propagation.test.ts (chainHost shape,
    // rebuild inline here); pattern: the full chain itself with end0/end1 as
    // boundary. Every candidate set is a singleton after propagation, so the
    // search places each of the pattern's elements exactly once:
    // 1 root region + 5 nodes + 4 wires = 10 placements, and the root loop
    // probes exactly the 1 host region.
    const host = /* chainHost() inline */
    const pattern = mkDiagramWithBoundary(/* same graph, ids prefixed p, boundary ['pend0', 'pend1'] */)
    const result = findOccurrences(host, pattern, {})
    expect(result.matches).toHaveLength(1)
    expect(result.status).toBe('complete')
    expect(result.explorationSteps).toBe(10)
  })

  it('symmetric boundary wires yield exactly the distinct attachment vectors', () => {
    // Host: identity j (arity 2) with wires u (j<->pinU), v (j<->pinV).
    // Pattern: identity (arity 2) with boundary wires x, y.
    // The two assignments {x->u,y->v} and {x->v,y->u} have distinct
    // attachment vectors [u,v] and [v,u]: both are real occurrences.
    const result = findOccurrences(host, pattern, {})
    expect(result.matches.map((m) => [...m.attachments]).sort()).toEqual([['u', 'v'], ['v', 'u']])
  })
})
```

Write both fixtures out in full (copy the chainHost literal; the symmetric fixture is six lines of nodes/wires). The step-count expectation is DERIVED, not tuned: count the pattern's regions+nodes+wires and the root probes, and write that arithmetic in a comment next to the assertion. If the engine's actual count differs, first recount from the engine's spend points; the number in the test must be the provably minimal placement count, and the engine must achieve it on this fixture — a higher measured count is an engine defect (a dead branch was entered), not a test to relax.

- [ ] **Step 2: Run to verify current status**

Run: `npx vitest run tests/kernel/diagram/match-adversarial.test.ts --config vitest.config.ts`
Expected: the two new tests PASS if Task 8's engine is right; if the step-count test fails, debug per the note above before proceeding.

- [ ] **Step 3: Fuel budget audit**

For each of the three `findOccurrences` call sites, decide the budget from the new step semantics (one placement per element per branch; rigid patterns ≈ pattern size × host root count):
- `src/app/interact/cite.ts:70` — trace where `fuel` comes from (caller/UI); if it is a constant, justify or replace it with a value derived from pattern×host size with the derivation in a comment.
- `src/app/define.ts:96-99` — `explorationFuel: 64` predates the rewrite; replace with a derived bound (e.g. `patternElements * hostRegionCount * safetyFactorJustifiedInComment`) — no unexplained constants (repo edict: every threshold needs a principled justification).
- `src/kernel/rules/iteration.ts` — same audit for the fuel its caller passes in (trace to its origin).

Each changed budget gets a comment stating the derivation. If a budget turns out to be caller-supplied policy (UI responsiveness), leave it and note that in the task report.

- [ ] **Step 4: Typecheck and full suite**

Run: `npm run typecheck && npm test`
Expected: green.

- [ ] **Step 5: Commit**

```bash
git add tests/kernel/diagram/match-adversarial.test.ts src/app/interact/cite.ts src/app/define.ts src/kernel/rules/iteration.ts
git commit -m "test: derived step-count and symmetry contracts; principled fuel budgets"
```

---

### Task 10: Final sweep

**Files:**
- Verify only (modify anything the sweep catches).

- [ ] **Step 1: Dead-reference sweep**

Run: `rg -n "exploreForm|exploreIso|exploreLabeling|boundaryForm|canonical/explore|resultFingerprint|editForm" src tests e2e docs/superpowers/plans docs/superpowers/specs`
Expected: hits ONLY in this plan file and the spec's historical prose. Any hit in src/tests/e2e is an unconverted consumer — convert it now.

- [ ] **Step 2: Full verification**

Run: `npm run typecheck && npm test`
Expected: green, full counts reported verbatim in the final report (no "should pass").
Then the e2e file touched in Task 5, if the environment allows: `npm run e2e -- e2e/interaction.spec.ts` — report actual result or the exact blocked command.

- [ ] **Step 3: Commit any sweep fixes**

```bash
git add <exact files the sweep changed>
git commit -m "chore: post-rework reference sweep"
```

---

## Self-Review Results

- **Spec coverage:** §1 rulings → Tasks 2 (ring/hub/dormancy tests) and 3 (arg order kept). §2 engine → Task 1. §3 pairwise iso → Task 2. §4 conversions/deletions → Tasks 4, 5, 6. §5 retained labeling → Task 3. §6 matcher → Tasks 7, 8 (with the flagged §6 amendment in Task 7 Step 5). §7 fuel → Task 9. §8 tests → Tasks 2, 8, 9 (+ existing suites as gates). §9 out-of-scope respected (no orbit pruning in wire-order; no automorphism collapsing in the matcher).
- **Placeholder scan:** engine bodies in Tasks 1, 3, 7, 8 are specified as verbatim ports of named line ranges of existing code plus complete behavioral contracts — the referenced code exists in-repo and the tests are written out; no TBDs.
- **Type consistency:** `Mark {side, sort, id, token}`, `RefinementSide {diagram, pins}`, `SideColors`, `buildRefineIndex`, `refineJointly` (Task 1) are used with those exact shapes in Tasks 2, 3, 7. `diagramIso`/`sameDiagram`/`DiagramIso`/`__isoCounters` (Task 2) match Tasks 4, 5, 6. `canonicalWireOrder` (Task 3) matches define.ts usage. `__makePropagationContext`/`__initCandidates`/`__propagate`/`CandidateSets` (Task 7) match Task 8's engine description.
