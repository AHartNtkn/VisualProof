# Plan 9: View Layer — Tromp Geometry, Physics, Rendering Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** The visual layer: λ-terms rendered as Tromp diagrams bent into incomplete circles (spec option A), regions as nested shaded circles, wires as identity stars; a self-organizing always-settling physics whose ONLY state is node positions; a pure display-list renderer with a thin canvas adapter and a vite demo page; and the mechanical layer-separation check (spec §4.2) that makes the kernel's independence machine-enforced.

**Architecture:** Everything lives in `src/view/` and depends one-way on `src/kernel/`. The pipeline is pure stages: `Term → TrompGrid` (integer grid: binder bars, stems, application bars, port rails) → `NodeGeometry` (polar bend: arcs/radials/anchors in node-local coordinates) → `Scene` (diagram + node positions → region circles derived bottom-up, wire stars through anchors) → `Shape[]` (display list with parity shading and golden-angle binder hues) → canvas (thin adapter, untested browser glue). Physics owns a `Map<NodeId, Vec2>` of positions + velocities and NOTHING else — region circles and wire paths are derived every frame, so there is nothing layout-shaped that could ever be saved. A vitest architecture test scans imports and fails loudly on any kernel→view edge.

**Tech Stack:** TypeScript strict, Vitest, vite (devDependency, for the demo page only), Canvas 2D (browser built-in — zero runtime deps preserved).

---

## Design decisions (read before implementing)

**Layer separation is machine-checked from this plan on.** `tests/architecture/layering.test.ts` walks `src/` and asserts: no file under `src/kernel/` imports from `src/view/`; no file under `src/view/` is imported by kernel JSON/store code (subsumed by the first rule); `src/view/canvas.ts` is the only module allowed to mention `CanvasRenderingContext2D`. Physics state is a runtime `Map` that no serializer touches — the spec's "layout is NEVER saved" needs no runtime guard because nothing in the kernel's file format can express it (enforced by the import check).

**Tromp grid, then bend.** The classic rectilinear Tromp layout is computed first on an integer grid: each `lam` is a horizontal bar at row = its binder depth; each `bvar` occurrence is a vertical stem from its binder's bar down into the application structure; each `app` places fn and arg side by side and joins their output stems with a bar one row below the deeper of the two; the term's output stem exits one row below everything. Free ports get RAILS stacked above row 0 (rows −1, −2, … in `freePorts` first-occurrence order) spanning their occurrence columns, each with drop stems to its occurrences — one rail per distinct port name, matching `requiredPorts` (one freeVar port per name). Constants are glyphs with output stems (opaque, rule 7 territory).

The bend (option A) maps grid → polar: column → angle within `[gap/2, 2π − gap/2]` (the gap is centered on angle 0), row → radius decreasing inward (rails at negative rows land OUTSIDE the rim — the radial pierce). Binder bars become concentric rim arcs (outermost binder = outermost arc); the application structure curls inward; each rail emits one outward pierce radial whose tip is the port's wire anchor; the output stem runs to the innermost ring, arcs to the gap edge, and exits straight through the gap to the output anchor at angle 0. Binder hue identity is the bar's row (stems carry their binder's row), rendered with golden-angle hues; tether-on-hover is Plan 10 interaction.

**Physics owns node positions only.** `PhysicsState = { positions, velocities }` keyed by NodeId. Everything else is DERIVED per frame: region circles are smallest-enclosing-circle-ish bounds of their contents (children first, bottom-up) plus padding; wire paths are stars from the endpoint-anchor centroid. Forces: all-pairs node repulsion, wire-spring attraction of endpoint nodes toward their wire's centroid, weak per-region cohesion toward the region's content centroid, sibling-region separation (computed circles that overlap push their contents apart), and velocity damping. Semi-implicit Euler at fixed dt; `settled` when max speed < ε; `settle` runs to settlement under a tick budget that fails LOUDLY when exhausted (fuel honesty). Seeding is deterministic (index-based golden-angle placement) — no randomness anywhere, so layouts are reproducible and tests exact.

**On physics constants:** the force coefficients are NOT correctness heuristics — any positive values yield a valid equilibrium of the same constraint system; they tune visual pacing only. They live in one `PhysicsParams` object with documented defaults, and the tests assert structural invariants (settling, separation, determinism), never specific coordinates.

**Renderer is a pure display list.** `renderScene(scene): Shape[]` — circles for regions (negative-polarity regions get a translucent fill; bubbles get a distinct stroke), wire stars as polylines, node arcs/radials with binder hues, glyph labels. Paint order: regions outer-first, wires, nodes. The canvas adapter (`drawShapes`) is the only DOM-touching module and stays untested glue; the demo page (`demo/`) builds a sample diagram, steps physics each frame, and draws.

**File map:**
- Create: `tests/architecture/layering.test.ts`
- Create: `src/view/vec.ts`, `src/view/tromp.ts`, `src/view/bend.ts`, `src/view/scene.ts`, `src/view/physics.ts`, `src/view/display.ts`, `src/view/canvas.ts`, `src/view/index.ts`
- Create: `demo/index.html`, `demo/main.ts`
- Modify: `package.json` (vite devDependency + `demo` script)
- Tests: `tests/view/{tromp,bend,scene,physics,display}.test.ts`

---

### Task 1: Mechanical layer-separation check

**Files:**
- Test: `tests/architecture/layering.test.ts`

- [ ] **Step 1: Write the test** (it must PASS against the current tree — it is a standing guard, not a bug reproduction)

`tests/architecture/layering.test.ts`:

```ts
import { describe, it, expect } from 'vitest'
import { readFileSync, readdirSync, statSync } from 'node:fs'
import { join } from 'node:path'

function tsFilesUnder(dir: string): string[] {
  const out: string[] = []
  for (const entry of readdirSync(dir)) {
    const full = join(dir, entry)
    if (statSync(full).isDirectory()) out.push(...tsFilesUnder(full))
    else if (entry.endsWith('.ts')) out.push(full)
  }
  return out
}

function importSpecifiers(file: string): string[] {
  const src = readFileSync(file, 'utf8')
  const specs: string[] = []
  const re = /from\s+['"]([^'"]+)['"]|import\s*\(\s*['"]([^'"]+)['"]\s*\)/g
  for (let m = re.exec(src); m !== null; m = re.exec(src)) {
    specs.push(m[1] ?? m[2]!)
  }
  return specs
}

describe('layer separation (spec §4.2)', () => {
  it('the kernel never imports from the view layer', () => {
    const offenders: string[] = []
    for (const file of tsFilesUnder('src/kernel')) {
      for (const spec of importSpecifiers(file)) {
        if (spec.includes('/view/') || spec.startsWith('../view') || spec.startsWith('../../view')) {
          offenders.push(`${file} imports '${spec}'`)
        }
      }
    }
    expect(offenders, offenders.join('\n')).toEqual([])
  })

  it('only the canvas adapter touches the canvas API', () => {
    const offenders: string[] = []
    for (const file of tsFilesUnder('src')) {
      if (file.endsWith('view/canvas.ts')) continue
      if (readFileSync(file, 'utf8').includes('CanvasRenderingContext2D')) {
        offenders.push(file)
      }
    }
    expect(offenders, offenders.join('\n')).toEqual([])
  })

  it('the kernel has no runtime dependencies on node built-ins beyond none at all', () => {
    // the kernel is pure data + algorithms: any node: import is a leak
    const offenders: string[] = []
    for (const file of tsFilesUnder('src/kernel')) {
      for (const spec of importSpecifiers(file)) {
        if (spec.startsWith('node:')) offenders.push(`${file} imports '${spec}'`)
      }
    }
    expect(offenders, offenders.join('\n')).toEqual([])
  })
})
```

- [ ] **Step 2: Run it** — `npx vitest run tests/architecture/layering.test.ts` — all three must PASS already (the kernel is clean today; this pins it).

- [ ] **Step 3: Commit**

```bash
git add tests/architecture/layering.test.ts
git commit -m "test(arch): mechanical layer-separation check (spec §4.2)"
```

---

### Task 2: Rectilinear Tromp grid

**Files:**
- Create: `src/view/vec.ts`
- Create: `src/view/tromp.ts`
- Test: `tests/view/tromp.test.ts`

- [ ] **Step 1: Write the failing tests**

`tests/view/tromp.test.ts`:

```ts
import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../src/kernel/term/parse'
import { trompGrid } from '../../src/view/tromp'

const consts = new Set(['C'])
const p = (s: string) => parseTerm(s, consts)

describe('trompGrid', () => {
  it('lays out the identity: one binder bar, one stem, one output', () => {
    const g = trompGrid(p('\\x. x'))
    expect(g.cols).toBe(1)
    expect(g.railRows).toBe(0)
    expect(g.bars).toEqual([{ row: 0, colStart: 0, colEnd: 0, kind: 'lam' }])
    // the variable stem hangs from the row-0 bar; the output exits below
    expect(g.stems).toContainEqual({ col: 0, rowTop: 0, rowBottom: 1, kind: 'var' })
    expect(g.stems).toContainEqual({ col: 0, rowTop: 1, rowBottom: 2, kind: 'output' })
    expect(g.outputCol).toBe(0)
  })

  it('stacks binder bars by depth and hangs each variable from its own binder', () => {
    const g = trompGrid(p('\\x. \\y. x'))
    expect(g.bars).toContainEqual({ row: 0, colStart: 0, colEnd: 0, kind: 'lam' })
    expect(g.bars).toContainEqual({ row: 1, colStart: 0, colEnd: 0, kind: 'lam' })
    // x is bound by the OUTER binder (row 0), entered at depth 2
    expect(g.stems).toContainEqual({ col: 0, rowTop: 0, rowBottom: 2, kind: 'var' })
  })

  it('an application joins the two output stems with a bar one row below the deeper side', () => {
    const g = trompGrid(p('(\\x. x) (\\x. x)'))
    expect(g.cols).toBe(2)
    // both identity boxes bottom out at row 1; the app bar sits at row 2
    expect(g.bars).toContainEqual({ row: 2, colStart: 0, colEnd: 1, kind: 'app' })
    expect(g.stems).toContainEqual({ col: 0, rowTop: 1, rowBottom: 2, kind: 'output' })
    expect(g.stems).toContainEqual({ col: 1, rowTop: 1, rowBottom: 2, kind: 'output' })
    expect(g.outputCol).toBe(0) // the function side carries the result
  })

  it('gives every distinct free port one rail above row 0, in first-occurrence order', () => {
    const g = trompGrid(p('y (z y)'))
    expect(g.railRows).toBe(2)
    const yRail = g.rails.find((r) => r.name === 'y')!
    const zRail = g.rails.find((r) => r.name === 'z')!
    expect(yRail.row).toBe(-1) // first occurrence
    expect(zRail.row).toBe(-2)
    // y occurs at columns 0 and 2: its rail spans them, with a drop at each
    expect(yRail.colStart).toBe(0)
    expect(yRail.colEnd).toBe(2)
    expect(g.stems.filter((s) => s.kind === 'port' && s.portName === 'y' && s.rowTop === -1)).toHaveLength(2)
  })

  it('renders constants as glyphs with output stems', () => {
    const g = trompGrid(p('C y'))
    expect(g.glyphs).toEqual([{ col: 0, row: 0, constId: 'C' }])
    expect(g.outputCol).toBe(0)
  })

  it('every stem and bar stays inside the declared grid bounds', () => {
    const g = trompGrid(p('\\f. \\x. f (f (f x))'))
    for (const b of g.bars) {
      expect(b.colStart).toBeGreaterThanOrEqual(0)
      expect(b.colEnd).toBeLessThan(g.cols)
      expect(b.row).toBeGreaterThanOrEqual(-g.railRows)
      expect(b.row).toBeLessThan(g.rows)
    }
    for (const s of g.stems) {
      expect(s.col).toBeGreaterThanOrEqual(0)
      expect(s.col).toBeLessThan(g.cols)
      expect(s.rowTop).toBeLessThanOrEqual(s.rowBottom)
      expect(s.rowBottom).toBeLessThanOrEqual(g.rows)
    }
  })

  it('no two bars overlap on the same row', () => {
    const g = trompGrid(p('(\\x. x x) (\\y. y) (z z)'))
    const byRow = new Map<number, { s: number; e: number }[]>()
    for (const b of g.bars) {
      const list = byRow.get(b.row) ?? []
      for (const o of list) {
        expect(b.colStart > o.e || b.colEnd < o.s).toBe(true)
      }
      list.push({ s: b.colStart, e: b.colEnd })
      byRow.set(b.row, list)
    }
  })
})
```

- [ ] **Step 2: Run tests to verify they fail**

Run: `npx vitest run tests/view/tromp.test.ts`
Expected: FAIL — cannot resolve `view/tromp`.

- [ ] **Step 3: Implement**

`src/view/vec.ts`:

```ts
export type Vec2 = { readonly x: number; readonly y: number }

export function vec(x: number, y: number): Vec2 {
  return { x, y }
}

export function add(a: Vec2, b: Vec2): Vec2 {
  return { x: a.x + b.x, y: a.y + b.y }
}

export function sub(a: Vec2, b: Vec2): Vec2 {
  return { x: a.x - b.x, y: a.y - b.y }
}

export function scale(a: Vec2, k: number): Vec2 {
  return { x: a.x * k, y: a.y * k }
}

export function length(a: Vec2): number {
  return Math.hypot(a.x, a.y)
}

export function polar(angle: number, r: number): Vec2 {
  return { x: Math.cos(angle) * r, y: Math.sin(angle) * r }
}
```

`src/view/tromp.ts`:

```ts
import type { Term } from '../kernel/term/term'
import { freePorts } from '../kernel/term/term'

export type Bar = {
  readonly row: number
  readonly colStart: number
  readonly colEnd: number
  readonly kind: 'lam' | 'app' | 'rail'
}

export type Stem = {
  readonly col: number
  readonly rowTop: number
  readonly rowBottom: number
  readonly kind: 'var' | 'output' | 'port'
  readonly portName?: string
}

export type Glyph = { readonly col: number; readonly row: number; readonly constId: string }

export type Rail = {
  readonly name: string
  readonly row: number
  readonly colStart: number
  readonly colEnd: number
  readonly stemCol: number
}

/**
 * Classic rectilinear Tromp layout on an integer grid. Binder bars sit at
 * row = binder depth (outermost = 0); variables hang from their binder's bar;
 * an application joins its two output stems one row below the deeper side;
 * free ports get rails stacked ABOVE row 0 (negative rows) in first-occurrence
 * order, one per distinct name — exactly mirroring requiredPorts.
 */
export type TrompGrid = {
  readonly cols: number
  /** Rows 0..rows: binder block + application structure + final output row. */
  readonly rows: number
  /** Port rails occupy rows -1..-railRows. */
  readonly railRows: number
  readonly bars: readonly Bar[]
  readonly stems: readonly Stem[]
  readonly glyphs: readonly Glyph[]
  readonly outputCol: number
  readonly rails: readonly Rail[]
}

type Box = {
  readonly width: number
  readonly bottom: number
  readonly stemCol: number
  readonly bars: readonly Bar[]
  readonly stems: readonly Stem[]
  readonly glyphs: readonly Glyph[]
  readonly ports: ReadonlyMap<string, readonly number[]>
}

function shifted(b: Box, dc: number): Box {
  if (dc === 0) return b
  return {
    width: b.width,
    bottom: b.bottom,
    stemCol: b.stemCol + dc,
    bars: b.bars.map((x) => ({ ...x, colStart: x.colStart + dc, colEnd: x.colEnd + dc })),
    stems: b.stems.map((x) => ({ ...x, col: x.col + dc })),
    glyphs: b.glyphs.map((x) => ({ ...x, col: x.col + dc })),
    ports: new Map([...b.ports].map(([n, cols]) => [n, cols.map((c) => c + dc)])),
  }
}

function mergePorts(a: ReadonlyMap<string, readonly number[]>, b: ReadonlyMap<string, readonly number[]>): Map<string, readonly number[]> {
  const out = new Map<string, readonly number[]>(a)
  for (const [n, cols] of b) out.set(n, [...(out.get(n) ?? []), ...cols])
  return out
}

function layoutAt(t: Term, depth: number): Box {
  switch (t.kind) {
    case 'bvar': {
      // assertWellFormedTerm guarantees index < depth for diagram node terms
      const barRow = depth - 1 - t.index
      return {
        width: 1, bottom: depth, stemCol: 0, bars: [], glyphs: [], ports: new Map(),
        stems: [{ col: 0, rowTop: barRow, rowBottom: depth, kind: 'var' }],
      }
    }
    case 'port':
      return {
        width: 1, bottom: depth, stemCol: 0, bars: [], glyphs: [],
        ports: new Map([[t.name, [0]]]),
        // runs from row 0 down through the binder block; the rail drop above
        // row 0 is added at assembly once the rail row is known
        stems: depth > 0 ? [{ col: 0, rowTop: 0, rowBottom: depth, kind: 'port', portName: t.name }] : [],
      }
    case 'const':
      return {
        width: 1, bottom: depth, stemCol: 0, bars: [], ports: new Map(),
        glyphs: [{ col: 0, row: depth, constId: t.id }],
        stems: [],
      }
    case 'lam': {
      const inner = layoutAt(t.body, depth + 1)
      return {
        ...inner,
        bars: [...inner.bars, { row: depth, colStart: 0, colEnd: inner.width - 1, kind: 'lam' }],
      }
    }
    case 'app': {
      const f = layoutAt(t.fn, depth)
      const a = shifted(layoutAt(t.arg, depth), f.width)
      const barRow = Math.max(f.bottom, a.bottom) + 1
      return {
        width: f.width + a.width,
        bottom: barRow,
        stemCol: f.stemCol,
        bars: [...f.bars, ...a.bars, { row: barRow, colStart: f.stemCol, colEnd: a.stemCol, kind: 'app' }],
        stems: [
          ...f.stems, ...a.stems,
          { col: f.stemCol, rowTop: f.bottom, rowBottom: barRow, kind: 'output' },
          { col: a.stemCol, rowTop: a.bottom, rowBottom: barRow, kind: 'output' },
        ],
        glyphs: [...f.glyphs, ...a.glyphs],
        ports: mergePorts(f.ports, a.ports),
      }
    }
  }
}

export function trompGrid(t: Term): TrompGrid {
  const box = layoutAt(t, 0)
  const names = freePorts(t)
  const rails: Rail[] = names.map((name, i) => {
    const cols = box.ports.get(name)
    if (cols === undefined || cols.length === 0) {
      throw new Error(`port '${name}' has no occurrence columns; layout is inconsistent with freePorts`)
    }
    return {
      name,
      row: -(i + 1),
      colStart: Math.min(...cols),
      colEnd: Math.max(...cols),
      stemCol: Math.min(...cols),
    }
  })
  const drops: Stem[] = rails.flatMap((rail) =>
    (box.ports.get(rail.name) ?? []).map((col): Stem => ({
      col, rowTop: rail.row, rowBottom: 0, kind: 'port', portName: rail.name,
    })))
  const output: Stem = { col: box.stemCol, rowTop: box.bottom, rowBottom: box.bottom + 1, kind: 'output' }
  return {
    cols: box.width,
    rows: box.bottom + 1,
    railRows: rails.length,
    bars: [...box.bars, ...rails.map((r): Bar => ({ row: r.row, colStart: r.colStart, colEnd: r.colEnd, kind: 'rail' }))],
    stems: [...box.stems, ...drops, output],
    glyphs: box.glyphs,
    outputCol: box.stemCol,
    rails,
  }
}
```

- [ ] **Step 4: Verify PASS, full suite, typecheck**

- [ ] **Step 5: Commit**

```bash
git add src/view/vec.ts src/view/tromp.ts tests/view/tromp.test.ts
git commit -m "feat(view): rectilinear Tromp grid layout"
```

---

### Task 3: Polar bend + node geometry

**Files:**
- Create: `src/view/bend.ts`
- Test: `tests/view/bend.test.ts`

- [ ] **Step 1: Write the failing tests**

`tests/view/bend.test.ts`:

```ts
import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../src/kernel/term/parse'
import { trompGrid } from '../../src/view/tromp'
import { bendGrid, atomGeometry, GAP_ANGLE } from '../../src/view/bend'
import { length } from '../../src/view/vec'

const noConsts = new Set<string>()
const p = (s: string) => parseTerm(s, noConsts)

describe('bendGrid', () => {
  it('maps binder bars to rim arcs, outermost binder outermost', () => {
    const g = bendGrid(trompGrid(p('\\x. \\y. x')))
    const lamArcs = g.arcs.filter((a) => a.kind === 'lam')
    expect(lamArcs).toHaveLength(2)
    const outer = lamArcs.find((a) => a.hueRow === 0)!
    const inner = lamArcs.find((a) => a.hueRow === 1)!
    expect(outer.r).toBeGreaterThan(inner.r)
  })

  it('keeps every angle inside the C (the gap is empty)', () => {
    const g = bendGrid(trompGrid(p('\\f. \\x. f (f x)')))
    const lo = GAP_ANGLE / 2
    const hi = 2 * Math.PI - GAP_ANGLE / 2
    for (const a of g.arcs) {
      expect(a.a0).toBeGreaterThanOrEqual(lo)
      expect(a.a1).toBeLessThanOrEqual(hi)
    }
    for (const r of g.radials) {
      expect(r.angle).toBeGreaterThanOrEqual(lo)
      expect(r.angle).toBeLessThanOrEqual(hi)
    }
  })

  it('port anchors pierce the rim radially: anchor radius exceeds every arc radius', () => {
    const g = bendGrid(trompGrid(p('y (z y)')))
    const maxArcR = Math.max(...g.arcs.map((a) => a.r))
    for (const name of ['y', 'z']) {
      expect(length(g.portAnchors[name]!)).toBeGreaterThan(maxArcR)
    }
  })

  it('the output anchor sits in the gap at angle 0, outside the rim', () => {
    const g = bendGrid(trompGrid(p('\\x. x')))
    expect(g.outputAnchor.y).toBeCloseTo(0, 10)
    expect(g.outputAnchor.x).toBeGreaterThan(0)
    const maxArcR = Math.max(...g.arcs.map((a) => a.r))
    expect(length(g.outputAnchor)).toBeGreaterThan(maxArcR)
    // the exit path: an innermost arc to the gap edge plus a straight line out
    expect(g.exitArc).not.toBeNull()
    expect(g.exitLine).toHaveLength(2)
  })

  it('var radials inherit their binder row for hue identity', () => {
    const g = bendGrid(trompGrid(p('\\x. \\y. x')))
    const varRadial = g.radials.find((r) => r.kind === 'var')!
    expect(varRadial.hueRow).toBe(0) // bound by the outer binder
  })

  it('all radii stay positive (the disc center is never crossed)', () => {
    const g = bendGrid(trompGrid(p('(\\x. x x) (\\y. y y)')))
    for (const a of g.arcs) expect(a.r).toBeGreaterThan(0)
    for (const r of g.radials) {
      expect(r.r0).toBeGreaterThan(0)
      expect(r.r1).toBeGreaterThan(0)
    }
  })
})

describe('atomGeometry', () => {
  it('spreads arg anchors evenly and scales with arity', () => {
    const g2 = atomGeometry(2)
    expect(Object.keys(g2.portAnchors)).toEqual(['a0', 'a1'])
    const d0 = length(g2.portAnchors['a0']!)
    const d1 = length(g2.portAnchors['a1']!)
    expect(d0).toBeCloseTo(d1, 10)
    expect(atomGeometry(0).arcs.length).toBeGreaterThan(0) // still a visible disc
  })
})
```

- [ ] **Step 2: Run tests to verify they fail**

Run: `npx vitest run tests/view/bend.test.ts`
Expected: FAIL — cannot resolve `view/bend`.

- [ ] **Step 3: Implement**

`src/view/bend.ts`:

```ts
import type { Vec2 } from './vec'
import { polar } from './vec'
import type { TrompGrid } from './tromp'

/** Total angular width of the C-gap, centered on angle 0 (the output exit). */
export const GAP_ANGLE = Math.PI / 3

export type NodeArc = {
  readonly r: number
  readonly a0: number
  readonly a1: number
  readonly kind: 'lam' | 'app' | 'rail'
  /** Hue identity: the grid row of the bar (lam bars: binder identity). */
  readonly hueRow: number
}

export type NodeRadial = {
  readonly angle: number
  readonly r0: number
  readonly r1: number
  readonly kind: 'var' | 'output' | 'port'
  /** For var stems: the binder bar row they hang from; otherwise null. */
  readonly hueRow: number | null
}

export type NodeGeometry = {
  /** Radius enclosing everything including pierce stubs and the exit. */
  readonly outerRadius: number
  readonly arcs: readonly NodeArc[]
  readonly radials: readonly NodeRadial[]
  readonly glyphs: readonly { readonly pos: Vec2; readonly constId: string }[]
  readonly outputAnchor: Vec2
  readonly portAnchors: Readonly<Record<string, Vec2>>
  /** Innermost arc carrying the output around to the gap edge (null when the
      output column already sits at the first column next to the gap). */
  readonly exitArc: { readonly r: number; readonly a0: number; readonly a1: number } | null
  readonly exitLine: readonly [Vec2, Vec2]
}

/**
 * Bend a rectilinear Tromp grid into an incomplete circle (spec option A):
 * columns map to angles inside [gap/2, 2π − gap/2]; rows map to radii
 * decreasing inward, with port rails (negative rows) landing OUTSIDE the rim
 * as radial pierces; the output runs to the innermost ring, arcs to the gap
 * edge, and exits straight through the gap to an anchor at angle 0.
 */
export function bendGrid(g: TrompGrid): NodeGeometry {
  const a0 = GAP_ANGLE / 2
  const span = 2 * Math.PI - GAP_ANGLE
  const theta = (col: number): number => a0 + ((col + 0.5) / g.cols) * span
  // row 0 sits at radius rowsBelow + 2 so the innermost row keeps radius 2
  const r0 = g.rows + 2
  const radius = (row: number): number => r0 - row
  const rimR = radius(0) + g.railRows // outermost rail ring
  const pierceR = rimR + 1

  const arcs: NodeArc[] = g.bars.map((b) => ({
    r: radius(b.row),
    a0: theta(b.colStart),
    a1: theta(b.colEnd),
    kind: b.kind,
    hueRow: b.row,
  }))
  const radials: NodeRadial[] = g.stems.map((s) => ({
    angle: theta(s.col),
    r0: radius(s.rowTop),
    r1: radius(s.rowBottom),
    kind: s.kind,
    hueRow: s.kind === 'var' ? s.rowTop : null,
  }))
  // one outward pierce per rail, its tip being the port anchor
  const portAnchors: Record<string, Vec2> = {}
  for (const rail of g.rails) {
    const angle = theta(rail.stemCol)
    radials.push({ angle, r0: radius(rail.row), r1: pierceR, kind: 'port', hueRow: null })
    portAnchors[rail.name] = polar(angle, pierceR)
  }
  // output exit: innermost ring arc to the gap edge, then straight out
  const exitR = radius(g.rows)
  const outAngle = theta(g.outputCol)
  const exitArc = outAngle > a0 ? { r: exitR, a0, a1: outAngle } : null
  const outputAnchor = polar(0, pierceR)
  const exitLine: readonly [Vec2, Vec2] = [polar(a0, exitR), outputAnchor]

  const glyphs = g.glyphs.map((gl) => ({ pos: polar(theta(gl.col), radius(gl.row)), constId: gl.constId }))

  return {
    outerRadius: pierceR + 0.5,
    arcs,
    radials,
    glyphs,
    outputAnchor,
    portAnchors,
    exitArc,
    exitLine,
  }
}

/**
 * Atoms (relation-variable applications) have no term structure: a small
 * disc with arg anchors spread evenly around it. Anchor keys use portKey
 * spelling without the colon ('a0', 'a1', …) purely as local labels.
 */
export function atomGeometry(arity: number): NodeGeometry {
  const r = 2
  const pierce = r + 1
  const portAnchors: Record<string, Vec2> = {}
  const radials: NodeRadial[] = []
  for (let i = 0; i < arity; i++) {
    const angle = Math.PI / 2 + (i * 2 * Math.PI) / Math.max(arity, 1)
    portAnchors[`a${i}`] = polar(angle, pierce)
    radials.push({ angle, r0: r, r1: pierce, kind: 'port', hueRow: null })
  }
  return {
    outerRadius: pierce + 0.5,
    arcs: [{ r, a0: 0, a1: 2 * Math.PI, kind: 'rail', hueRow: 0 }],
    radials,
    glyphs: [],
    outputAnchor: polar(0, pierce),
    portAnchors,
    exitArc: null,
    exitLine: [polar(0, r), polar(0, pierce)],
  }
}
```

- [ ] **Step 4: Verify PASS, full suite, typecheck**

- [ ] **Step 5: Commit**

```bash
git add src/view/bend.ts tests/view/bend.test.ts
git commit -m "feat(view): polar bend into the option-A incomplete circle"
```

---

### Task 4: Scene derivation

**Files:**
- Create: `src/view/scene.ts`
- Test: `tests/view/scene.test.ts`

- [ ] **Step 1: Write the failing tests**

`tests/view/scene.test.ts`:

```ts
import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../src/kernel/term/parse'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { buildScene } from '../../src/view/scene'
import { vec, length, sub } from '../../src/view/vec'

const noConsts = new Set<string>()
const p = (s: string) => parseTerm(s, noConsts)

function host() {
  const h = new DiagramBuilder()
  const n = h.termNode(h.root, p('y'))
  const cut = h.cut(h.root)
  const m = h.termNode(cut, p('\\x. x'))
  const w = h.wire(h.root, [
    { node: n, port: { kind: 'freeVar', name: 'y' } },
    { node: m, port: { kind: 'output' } },
  ])
  const bub = h.bubble(cut, 1)
  const atom = h.atom(bub, bub)
  h.wire(cut, [{ node: atom, port: { kind: 'arg', index: 0 } }])
  return { d: h.build(), n, cut, m, w, bub, atom }
}

describe('buildScene', () => {
  it('derives region circles bottom-up: every region encloses its contents', () => {
    const { d, n, m, atom, cut, bub } = host()
    const pos = new Map([[n, vec(0, 0)], [m, vec(40, 0)], [atom, vec(60, 0)]])
    const scene = buildScene(d, pos)
    const byId = new Map(scene.regions.map((r) => [r.id, r]))
    for (const sn of scene.nodes) {
      const region = byId.get(d.nodes[sn.id]!.region)!
      const need = length(sub(sn.center, region.center)) + sn.geometry.outerRadius
      expect(region.radius).toBeGreaterThanOrEqual(need)
    }
    // nesting: the bubble circle lies inside the cut circle
    const cutCircle = byId.get(cut)!
    const bubCircle = byId.get(bub)!
    const dist = length(sub(bubCircle.center, cutCircle.center))
    expect(dist + bubCircle.radius).toBeLessThanOrEqual(cutCircle.radius + 1e-9)
  })

  it('shades exactly the negative regions', () => {
    const { d, n, m, atom } = host()
    const pos = new Map([[n, vec(0, 0)], [m, vec(40, 0)], [atom, vec(60, 0)]])
    const scene = buildScene(d, pos)
    for (const r of scene.regions) {
      const expected = d.regions[r.id]!.kind === 'cut' // depth-1 cut is the only negative region here
      expect(r.shaded).toBe(expected)
    }
  })

  it('wire stars pass through the endpoint anchors', () => {
    const { d, n, m, atom, w } = host()
    const pos = new Map([[n, vec(0, 0)], [m, vec(40, 0)], [atom, vec(60, 0)]])
    const scene = buildScene(d, pos)
    const star = scene.wires.find((x) => x.id === w)!
    expect(star.spokes).toHaveLength(2)
    // the hub is the centroid of the spokes
    const cx = (star.spokes[0]!.x + star.spokes[1]!.x) / 2
    expect(star.hub.x).toBeCloseTo(cx, 10)
  })

  it('zero-endpoint wires render as a hub at their scope center', () => {
    const h = new DiagramBuilder()
    h.wire(h.root, [])
    const d = h.build()
    const scene = buildScene(d, new Map())
    expect(scene.wires).toHaveLength(1)
    expect(scene.wires[0]!.spokes).toHaveLength(0)
  })

  it('rejects positions for unknown nodes and missing positions, loudly', () => {
    const { d, n, m, atom } = host()
    expect(() => buildScene(d, new Map([[n, vec(0, 0)], [m, vec(1, 0)]])))
      .toThrowError(new RegExp(`no position for node '${atom}'`))
    expect(() => buildScene(d, new Map([[n, vec(0, 0)], [m, vec(1, 0)], [atom, vec(2, 0)], ['ghost', vec(3, 0)]])))
      .toThrowError(/position for unknown node 'ghost'/)
  })
})
```

- [ ] **Step 2: Run tests to verify they fail**

Run: `npx vitest run tests/view/scene.test.ts`
Expected: FAIL — cannot resolve `view/scene`.

- [ ] **Step 3: Implement**

`src/view/scene.ts`:

```ts
import type { Diagram, NodeId, RegionId, WireId, Port } from '../kernel/diagram/diagram'
import { portKey } from '../kernel/diagram/diagram'
import { polarity } from '../kernel/diagram/regions'
import type { Vec2 } from './vec'
import { add, scale, sub, length, vec } from './vec'
import type { NodeGeometry } from './bend'
import { bendGrid, atomGeometry } from './bend'
import { trompGrid } from './tromp'

export type SceneRegion = {
  readonly id: RegionId
  readonly kind: 'sheet' | 'cut' | 'bubble'
  readonly center: Vec2
  readonly radius: number
  readonly shaded: boolean
}

export type SceneNode = {
  readonly id: NodeId
  readonly center: Vec2
  readonly geometry: NodeGeometry
}

export type SceneWire = {
  readonly id: WireId
  readonly hub: Vec2
  readonly spokes: readonly Vec2[]
}

export type Scene = {
  readonly regions: readonly SceneRegion[]
  readonly nodes: readonly SceneNode[]
  readonly wires: readonly SceneWire[]
}

const REGION_PADDING = 3

/** The world-space wire anchor of (node, port) given the node's center. */
export function anchorOf(geometry: NodeGeometry, center: Vec2, port: Port): Vec2 {
  if (port.kind === 'output') return add(center, geometry.outputAnchor)
  const key = port.kind === 'freeVar' ? port.name : `a${port.index}`
  const local = geometry.portAnchors[key]
  if (local === undefined) {
    throw new Error(`geometry has no anchor for port '${portKey(port)}'`)
  }
  return add(center, local)
}

export function nodeGeometry(d: Diagram, id: NodeId): NodeGeometry {
  const n = d.nodes[id]
  if (n === undefined) throw new Error(`unknown node '${id}'`)
  if (n.kind === 'term') return bendGrid(trompGrid(n.term))
  const binder = d.regions[n.binder]!
  return atomGeometry(binder.kind === 'bubble' ? binder.arity : 0)
}

/**
 * Derive the full scene from the diagram and the physics-owned node
 * positions — the ONLY layout state in the system. Region circles are
 * computed bottom-up to enclose their contents plus padding; wires are stars
 * through their endpoint anchors. Pure: same inputs, same scene.
 */
export function buildScene(d: Diagram, positions: ReadonlyMap<NodeId, Vec2>): Scene {
  for (const id of positions.keys()) {
    if (d.nodes[id] === undefined) throw new Error(`position for unknown node '${id}'`)
  }
  const geometries = new Map<NodeId, NodeGeometry>()
  const centers = new Map<NodeId, Vec2>()
  for (const id of Object.keys(d.nodes)) {
    const pos = positions.get(id)
    if (pos === undefined) throw new Error(`no position for node '${id}'`)
    geometries.set(id, nodeGeometry(d, id))
    centers.set(id, pos)
  }

  // region circles, children-first (bottom-up over the region tree)
  const children = new Map<RegionId, RegionId[]>()
  for (const id of Object.keys(d.regions)) children.set(id, [])
  for (const [id, r] of Object.entries(d.regions)) {
    if (r.kind !== 'sheet') children.get(r.parent)!.push(id)
  }
  const nodesIn = new Map<RegionId, NodeId[]>()
  for (const id of Object.keys(d.regions)) nodesIn.set(id, [])
  for (const [id, n] of Object.entries(d.nodes)) nodesIn.get(n.region)!.push(id)

  const circles = new Map<RegionId, { center: Vec2; radius: number }>()
  const computeCircle = (id: RegionId): { center: Vec2; radius: number } => {
    const cached = circles.get(id)
    if (cached !== undefined) return cached
    const content: { center: Vec2; radius: number }[] = [
      ...nodesIn.get(id)!.map((n) => ({ center: centers.get(n)!, radius: geometries.get(n)!.outerRadius })),
      ...children.get(id)!.map((c) => computeCircle(c)),
    ]
    let circle: { center: Vec2; radius: number }
    if (content.length === 0) {
      circle = { center: vec(0, 0), radius: REGION_PADDING }
    } else {
      let center = vec(0, 0)
      for (const c of content) center = add(center, c.center)
      center = scale(center, 1 / content.length)
      const radius = Math.max(...content.map((c) => length(sub(c.center, center)) + c.radius)) + REGION_PADDING
      circle = { center, radius }
    }
    circles.set(id, circle)
    return circle
  }
  for (const id of Object.keys(d.regions)) computeCircle(id)

  const regions: SceneRegion[] = Object.entries(d.regions).map(([id, r]) => ({
    id,
    kind: r.kind,
    center: circles.get(id)!.center,
    radius: circles.get(id)!.radius,
    shaded: polarity(d, id) === 'negative',
  }))

  const nodes: SceneNode[] = Object.keys(d.nodes).map((id) => ({
    id,
    center: centers.get(id)!,
    geometry: geometries.get(id)!,
  }))

  const wires: SceneWire[] = Object.entries(d.wires).map(([id, w]) => {
    const spokes = w.endpoints.map((ep) => anchorOf(geometries.get(ep.node)!, centers.get(ep.node)!, ep.port))
    let hub: Vec2
    if (spokes.length === 0) {
      hub = circles.get(w.scope)!.center
    } else {
      let c = vec(0, 0)
      for (const s of spokes) c = add(c, s)
      hub = scale(c, 1 / spokes.length)
    }
    return { id, hub, spokes }
  })

  return { regions, nodes, wires }
}
```

- [ ] **Step 4: Verify PASS, full suite, typecheck**

- [ ] **Step 5: Commit**

```bash
git add src/view/scene.ts tests/view/scene.test.ts
git commit -m "feat(view): scene derivation — region circles and wire stars from node positions"
```

---

### Task 5: Physics

**Files:**
- Create: `src/view/physics.ts`
- Test: `tests/view/physics.test.ts`

- [ ] **Step 1: Write the failing tests**

`tests/view/physics.test.ts`:

```ts
import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../src/kernel/term/parse'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { initialState, step, settle, settled, DEFAULT_PARAMS } from '../../src/view/physics'
import { buildScene } from '../../src/view/scene'
import { length, sub } from '../../src/view/vec'

const noConsts = new Set<string>()
const p = (s: string) => parseTerm(s, noConsts)

function host() {
  const h = new DiagramBuilder()
  const a = h.termNode(h.root, p('y'))
  const b = h.termNode(h.root, p('\\x. x'))
  h.wire(h.root, [
    { node: a, port: { kind: 'freeVar', name: 'y' } },
    { node: b, port: { kind: 'output' } },
  ])
  const cut1 = h.cut(h.root)
  const c = h.termNode(cut1, p('\\x. x'))
  const cut2 = h.cut(h.root)
  const e = h.termNode(cut2, p('\\x. \\y. x'))
  void c
  void e
  return h.build()
}

describe('physics', () => {
  it('seeds deterministically: every node gets a distinct position', () => {
    const d = host()
    const s1 = initialState(d)
    const s2 = initialState(d)
    expect([...s1.positions.entries()]).toEqual([...s2.positions.entries()])
    const seen = new Set([...s1.positions.values()].map((v) => `${v.x},${v.y}`))
    expect(seen.size).toBe(Object.keys(d.nodes).length)
  })

  it('stepping is deterministic', () => {
    const d = host()
    let a = initialState(d)
    let b = initialState(d)
    for (let i = 0; i < 50; i++) {
      a = step(d, a, DEFAULT_PARAMS)
      b = step(d, b, DEFAULT_PARAMS)
    }
    expect([...a.positions.entries()]).toEqual([...b.positions.entries()])
  })

  it('settles within the tick budget and reports settlement', () => {
    const d = host()
    const s = settle(d, initialState(d), DEFAULT_PARAMS, 20000)
    expect(settled(s, DEFAULT_PARAMS)).toBe(true)
  })

  it('after settling, sibling region circles do not overlap', () => {
    const d = host()
    const s = settle(d, initialState(d), DEFAULT_PARAMS, 20000)
    const scene = buildScene(d, s.positions)
    const cuts = scene.regions.filter((r) => r.kind === 'cut')
    expect(cuts).toHaveLength(2)
    const [r1, r2] = cuts
    expect(length(sub(r1!.center, r2!.center))).toBeGreaterThanOrEqual(r1!.radius + r2!.radius - 1e-6)
  })

  it('after settling, no two nodes coincide', () => {
    const d = host()
    const s = settle(d, initialState(d), DEFAULT_PARAMS, 20000)
    const ps = [...s.positions.values()]
    for (let i = 0; i < ps.length; i++) {
      for (let j = i + 1; j < ps.length; j++) {
        expect(length(sub(ps[i]!, ps[j]!))).toBeGreaterThan(1)
      }
    }
  })

  it('fails loudly when the tick budget is exhausted', () => {
    const d = host()
    expect(() => settle(d, initialState(d), DEFAULT_PARAMS, 1))
      .toThrowError(/did not settle within 1 ticks/)
  })
})
```

- [ ] **Step 2: Run tests to verify they fail**

Run: `npx vitest run tests/view/physics.test.ts`
Expected: FAIL — cannot resolve `view/physics`.

- [ ] **Step 3: Implement**

`src/view/physics.ts`:

```ts
import type { Diagram, NodeId } from '../kernel/diagram/diagram'
import type { Vec2 } from './vec'
import { add, scale, sub, length, vec, polar } from './vec'
import { buildScene } from './scene'

/**
 * The physics layer's entire state: node positions and velocities. Nothing
 * here is semantic and nothing here is ever serialized (the kernel file
 * format cannot express it; the architecture test pins the import direction).
 */
export type PhysicsState = {
  readonly positions: ReadonlyMap<NodeId, Vec2>
  readonly velocities: ReadonlyMap<NodeId, Vec2>
}

/**
 * Force coefficients. These are NOT correctness heuristics: any positive
 * values give a valid equilibrium of the same constraint system (repulsion,
 * wire springs, cohesion, sibling separation); they tune visual pacing only.
 */
export type PhysicsParams = {
  readonly dt: number
  readonly damping: number
  readonly repulsion: number
  readonly minDistance: number
  readonly wireSpring: number
  readonly cohesion: number
  readonly separation: number
  readonly settleSpeed: number
}

export const DEFAULT_PARAMS: PhysicsParams = {
  dt: 0.05,
  damping: 4,
  repulsion: 400,
  minDistance: 4,
  wireSpring: 2,
  cohesion: 0.4,
  separation: 6,
  settleSpeed: 0.05,
}

const GOLDEN = Math.PI * (3 - Math.sqrt(5))

/**
 * Deterministic seeding: nodes spiral out from the origin in id-sorted order.
 * Arbitrary but deterministic and collision-free — the forces own the layout,
 * the seed only has to avoid coincident starts.
 */
export function initialState(d: Diagram): PhysicsState {
  const ids = Object.keys(d.nodes).sort()
  const positions = new Map<NodeId, Vec2>()
  const velocities = new Map<NodeId, Vec2>()
  ids.forEach((id, i) => {
    positions.set(id, polar(i * GOLDEN, 10 + 6 * i))
    velocities.set(id, vec(0, 0))
  })
  return { positions, velocities }
}

export function step(d: Diagram, s: PhysicsState, params: PhysicsParams): PhysicsState {
  const ids = Object.keys(d.nodes).sort()
  const force = new Map<NodeId, Vec2>(ids.map((id) => [id, vec(0, 0)]))
  const addForce = (id: NodeId, f: Vec2): void => {
    force.set(id, add(force.get(id)!, f))
  }
  const at = (id: NodeId): Vec2 => s.positions.get(id)!

  // all-pairs repulsion
  for (let i = 0; i < ids.length; i++) {
    for (let j = i + 1; j < ids.length; j++) {
      const a = ids[i]!
      const b = ids[j]!
      const delta = sub(at(a), at(b))
      const dist = Math.max(length(delta), params.minDistance)
      const dir = dist > 0 ? scale(delta, 1 / dist) : vec(1, 0)
      const f = scale(dir, params.repulsion / (dist * dist))
      addForce(a, f)
      addForce(b, scale(f, -1))
    }
  }

  // wire springs: endpoints pulled toward the wire centroid
  const scene = buildScene(d, s.positions)
  const wireById = new Map(scene.wires.map((w) => [w.id, w]))
  for (const [wid, w] of Object.entries(d.wires)) {
    const star = wireById.get(wid)!
    for (const ep of w.endpoints) {
      const pull = sub(star.hub, at(ep.node))
      addForce(ep.node, scale(pull, params.wireSpring))
    }
  }

  // per-region cohesion toward the content centroid
  const byRegion = new Map<string, NodeId[]>()
  for (const [id, n] of Object.entries(d.nodes)) {
    const list = byRegion.get(n.region) ?? []
    list.push(id)
    byRegion.set(n.region, list)
  }
  for (const members of byRegion.values()) {
    if (members.length < 2) continue
    let c = vec(0, 0)
    for (const m of members) c = add(c, at(m))
    c = scale(c, 1 / members.length)
    for (const m of members) addForce(m, scale(sub(c, at(m)), params.cohesion))
  }

  // sibling-region separation: overlapping derived circles push their contents apart
  const regionsById = new Map(scene.regions.map((r) => [r.id, r]))
  const siblings = new Map<string, string[]>()
  for (const [id, r] of Object.entries(d.regions)) {
    if (r.kind === 'sheet') continue
    const list = siblings.get(r.parent) ?? []
    list.push(id)
    siblings.set(r.parent, list)
  }
  const subtreeNodes = (root: string): NodeId[] => {
    const out: NodeId[] = []
    for (const [id, n] of Object.entries(d.nodes)) {
      let cur: string | null = n.region
      while (cur !== null) {
        if (cur === root) {
          out.push(id)
          break
        }
        const reg = d.regions[cur]!
        cur = reg.kind === 'sheet' ? null : reg.parent
      }
    }
    return out
  }
  for (const sibs of siblings.values()) {
    for (let i = 0; i < sibs.length; i++) {
      for (let j = i + 1; j < sibs.length; j++) {
        const ra = regionsById.get(sibs[i]!)!
        const rb = regionsById.get(sibs[j]!)!
        const delta = sub(ra.center, rb.center)
        const dist = Math.max(length(delta), 1e-6)
        const overlap = ra.radius + rb.radius - dist
        if (overlap <= 0) continue
        const dir = scale(delta, 1 / dist)
        const push = scale(dir, params.separation * overlap)
        for (const n of subtreeNodes(sibs[i]!)) addForce(n, push)
        for (const n of subtreeNodes(sibs[j]!)) addForce(n, scale(push, -1))
      }
    }
  }

  // semi-implicit Euler with damping
  const positions = new Map<NodeId, Vec2>()
  const velocities = new Map<NodeId, Vec2>()
  for (const id of ids) {
    const v0 = s.velocities.get(id)!
    const v1 = scale(add(v0, scale(force.get(id)!, params.dt)), Math.max(0, 1 - params.damping * params.dt))
    velocities.set(id, v1)
    positions.set(id, add(at(id), scale(v1, params.dt)))
  }
  return { positions, velocities }
}

export function settled(s: PhysicsState, params: PhysicsParams): boolean {
  for (const v of s.velocities.values()) {
    if (length(v) >= params.settleSpeed) return false
  }
  return true
}

/** Run to settlement under a tick budget; fail loudly when exhausted (fuel honesty). */
export function settle(d: Diagram, s0: PhysicsState, params: PhysicsParams, maxTicks: number): PhysicsState {
  let s = s0
  for (let i = 0; i < maxTicks; i++) {
    s = step(d, s, params)
    if (settled(s, params)) return s
  }
  throw new Error(`physics did not settle within ${maxTicks} ticks (last max speed above ${params.settleSpeed})`)
}
```

- [ ] **Step 4: Verify PASS, full suite, typecheck** (the settle tests are the slowest in the suite; if `settle` needs more than ~2s, report timings rather than weakening assertions)

- [ ] **Step 5: Commit**

```bash
git add src/view/physics.ts tests/view/physics.test.ts
git commit -m "feat(view): self-organizing physics over node positions only"
```

---

### Task 6: Display list, canvas adapter, demo

**Files:**
- Create: `src/view/display.ts`, `src/view/canvas.ts`, `src/view/index.ts`
- Create: `demo/index.html`, `demo/main.ts`
- Modify: `package.json` (add `vite` devDependency and `"demo": "vite demo"` script)
- Test: `tests/view/display.test.ts`

- [ ] **Step 1: Write the failing tests**

`tests/view/display.test.ts`:

```ts
import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../src/kernel/term/parse'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { buildScene } from '../../src/view/scene'
import { renderScene, binderHue } from '../../src/view/display'
import { initialState, settle, DEFAULT_PARAMS } from '../../src/view/physics'

const noConsts = new Set<string>()
const p = (s: string) => parseTerm(s, noConsts)

function scene() {
  const h = new DiagramBuilder()
  const n = h.termNode(h.root, p('\\x. \\y. x'))
  const cut = h.cut(h.root)
  const m = h.termNode(cut, p('y'))
  void n
  void m
  const d = h.build()
  const s = settle(d, initialState(d), DEFAULT_PARAMS, 20000)
  return buildScene(d, s.positions)
}

describe('renderScene', () => {
  it('paints regions first, then wires, then node structure', () => {
    const shapes = renderScene(scene())
    const firstNodeArc = shapes.findIndex((s) => s.kind === 'arc')
    const lastRegion = shapes.map((s) => s.kind).lastIndexOf('circle')
    const firstWire = shapes.findIndex((s) => s.kind === 'polyline')
    expect(lastRegion).toBeLessThan(firstWire)
    expect(firstWire).toBeLessThan(firstNodeArc)
  })

  it('fills exactly the shaded (negative) regions', () => {
    const shapes = renderScene(scene())
    const circles = shapes.filter((s) => s.kind === 'circle')
    expect(circles.filter((c) => c.kind === 'circle' && c.fill !== undefined)).toHaveLength(1)
  })

  it('binder hues are distinct per binder row and stable', () => {
    expect(binderHue(0)).not.toBe(binderHue(1))
    expect(binderHue(3)).toBe(binderHue(3))
  })

  it('every shape carries finite coordinates', () => {
    for (const s of renderScene(scene())) {
      const nums: number[] = []
      if (s.kind === 'circle') nums.push(s.center.x, s.center.y, s.r)
      if (s.kind === 'arc') nums.push(s.center.x, s.center.y, s.r, s.a0, s.a1)
      if (s.kind === 'segment') nums.push(s.from.x, s.from.y, s.to.x, s.to.y)
      if (s.kind === 'polyline') for (const pt of s.points) nums.push(pt.x, pt.y)
      if (s.kind === 'label') nums.push(s.pos.x, s.pos.y)
      for (const x of nums) expect(Number.isFinite(x)).toBe(true)
    }
  })
})
```

- [ ] **Step 2: Run tests to verify they fail**

Run: `npx vitest run tests/view/display.test.ts`
Expected: FAIL — cannot resolve `view/display`.

- [ ] **Step 3: Implement**

`src/view/display.ts`:

```ts
import type { Vec2 } from './vec'
import { add, polar } from './vec'
import type { Scene } from './scene'

export type Shape =
  | { readonly kind: 'circle'; readonly center: Vec2; readonly r: number; readonly stroke: string; readonly fill?: string }
  | { readonly kind: 'arc'; readonly center: Vec2; readonly r: number; readonly a0: number; readonly a1: number; readonly stroke: string; readonly width: number }
  | { readonly kind: 'segment'; readonly from: Vec2; readonly to: Vec2; readonly stroke: string; readonly width: number }
  | { readonly kind: 'polyline'; readonly points: readonly Vec2[]; readonly stroke: string; readonly width: number }
  | { readonly kind: 'label'; readonly pos: Vec2; readonly text: string; readonly color: string }

/** Golden-angle hue per binder row: distinct, stable, no configuration. */
export function binderHue(row: number): string {
  const hue = ((row * 137.508) % 360 + 360) % 360
  return `hsl(${hue.toFixed(1)}, 70%, 45%)`
}

const REGION_STROKE = '#444'
const NEGATIVE_FILL = 'rgba(60, 60, 80, 0.15)'
const BUBBLE_STROKE = '#7a4dbf'
const WIRE_STROKE = '#1f6f8b'
const STRUCTURE = '#222'

/**
 * Pure display list, paint-ordered: regions (outer first, negatives filled,
 * bubbles in the second-order stroke), wires, then node structure with
 * binder hues at rest (tethers-on-hover is interaction, Plan 10).
 */
export function renderScene(scene: Scene): Shape[] {
  const shapes: Shape[] = []
  const regions = [...scene.regions].sort((a, b) => b.radius - a.radius)
  for (const r of regions) {
    if (r.kind === 'sheet') continue
    shapes.push({
      kind: 'circle',
      center: r.center,
      r: r.radius,
      stroke: r.kind === 'bubble' ? BUBBLE_STROKE : REGION_STROKE,
      ...(r.shaded ? { fill: NEGATIVE_FILL } : {}),
    })
  }
  for (const w of scene.wires) {
    if (w.spokes.length === 0) {
      shapes.push({ kind: 'polyline', points: [w.hub, add(w.hub, polar(0, 2))], stroke: WIRE_STROKE, width: 1.5 })
      continue
    }
    for (const s of w.spokes) {
      shapes.push({ kind: 'polyline', points: [w.hub, s], stroke: WIRE_STROKE, width: 1.5 })
    }
  }
  for (const n of scene.nodes) {
    const g = n.geometry
    for (const a of g.arcs) {
      shapes.push({
        kind: 'arc', center: n.center, r: a.r, a0: a.a0, a1: a.a1,
        stroke: a.kind === 'lam' ? binderHue(a.hueRow) : STRUCTURE, width: a.kind === 'lam' ? 2 : 1.2,
      })
    }
    for (const r of g.radials) {
      shapes.push({
        kind: 'segment',
        from: add(n.center, polar(r.angle, r.r0)),
        to: add(n.center, polar(r.angle, r.r1)),
        stroke: r.hueRow === null ? STRUCTURE : binderHue(r.hueRow),
        width: 1.2,
      })
    }
    if (g.exitArc !== null) {
      shapes.push({ kind: 'arc', center: n.center, r: g.exitArc.r, a0: g.exitArc.a0, a1: g.exitArc.a1, stroke: STRUCTURE, width: 1.2 })
    }
    shapes.push({ kind: 'segment', from: add(n.center, g.exitLine[0]), to: add(n.center, g.exitLine[1]), stroke: STRUCTURE, width: 1.2 })
    for (const gl of g.glyphs) {
      shapes.push({ kind: 'label', pos: add(n.center, gl.pos), text: gl.constId, color: STRUCTURE })
    }
  }
  return shapes
}
```

`src/view/canvas.ts`:

```ts
import type { Shape } from './display'

/**
 * The only module that touches the canvas API — thin, untested browser glue.
 * The transform maps world units to device pixels.
 */
export function drawShapes(
  ctx: CanvasRenderingContext2D,
  shapes: readonly Shape[],
  transform: { readonly scale: number; readonly offsetX: number; readonly offsetY: number },
): void {
  const X = (x: number): number => x * transform.scale + transform.offsetX
  const Y = (y: number): number => y * transform.scale + transform.offsetY
  for (const s of shapes) {
    switch (s.kind) {
      case 'circle': {
        ctx.beginPath()
        ctx.arc(X(s.center.x), Y(s.center.y), s.r * transform.scale, 0, 2 * Math.PI)
        if (s.fill !== undefined) {
          ctx.fillStyle = s.fill
          ctx.fill()
        }
        ctx.strokeStyle = s.stroke
        ctx.lineWidth = 1
        ctx.stroke()
        break
      }
      case 'arc': {
        ctx.beginPath()
        ctx.arc(X(s.center.x), Y(s.center.y), s.r * transform.scale, s.a0, s.a1)
        ctx.strokeStyle = s.stroke
        ctx.lineWidth = s.width
        ctx.stroke()
        break
      }
      case 'segment': {
        ctx.beginPath()
        ctx.moveTo(X(s.from.x), Y(s.from.y))
        ctx.lineTo(X(s.to.x), Y(s.to.y))
        ctx.strokeStyle = s.stroke
        ctx.lineWidth = s.width
        ctx.stroke()
        break
      }
      case 'polyline': {
        if (s.points.length === 0) break
        ctx.beginPath()
        ctx.moveTo(X(s.points[0]!.x), Y(s.points[0]!.y))
        for (const pt of s.points.slice(1)) ctx.lineTo(X(pt.x), Y(pt.y))
        ctx.strokeStyle = s.stroke
        ctx.lineWidth = s.width
        ctx.stroke()
        break
      }
      case 'label': {
        ctx.fillStyle = s.color
        ctx.font = `${12}px sans-serif`
        ctx.fillText(s.text, X(s.pos.x), Y(s.pos.y))
        break
      }
    }
  }
}
```

`src/view/index.ts`:

```ts
export type { Vec2 } from './vec'
export { vec, add, sub, scale, length, polar } from './vec'
export type { TrompGrid, Bar, Stem, Glyph, Rail } from './tromp'
export { trompGrid } from './tromp'
export type { NodeGeometry, NodeArc, NodeRadial } from './bend'
export { bendGrid, atomGeometry, GAP_ANGLE } from './bend'
export type { Scene, SceneRegion, SceneNode, SceneWire } from './scene'
export { buildScene, nodeGeometry, anchorOf } from './scene'
export type { PhysicsState, PhysicsParams } from './physics'
export { initialState, step, settle, settled, DEFAULT_PARAMS } from './physics'
export type { Shape } from './display'
export { renderScene, binderHue } from './display'
export { drawShapes } from './canvas'
```

`demo/index.html`:

```html
<!doctype html>
<html>
  <head>
    <meta charset="utf-8" />
    <title>Visual Proof Assistant — view layer demo</title>
    <style>
      html, body { margin: 0; height: 100%; overflow: hidden; background: #fafaf7; }
      canvas { display: block; }
    </style>
  </head>
  <body>
    <canvas id="c"></canvas>
    <script type="module" src="./main.ts"></script>
  </body>
</html>
```

`demo/main.ts`:

```ts
import { parseTerm } from '../src/kernel/term/parse'
import { DiagramBuilder } from '../src/kernel/diagram/builder'
import { buildScene, initialState, step, renderScene, drawShapes, DEFAULT_PARAMS } from '../src/view/index'

const consts = new Set<string>()
const p = (s: string) => parseTerm(s, consts)

const h = new DiagramBuilder()
const a = h.termNode(h.root, p('y'))
const b = h.termNode(h.root, p('\\x. x'))
h.wire(h.root, [
  { node: a, port: { kind: 'freeVar', name: 'y' } },
  { node: b, port: { kind: 'output' } },
])
const cut = h.cut(h.root)
const c = h.termNode(cut, p('\\f. \\x. f (f x)'))
const bub = h.bubble(cut, 1)
const atom = h.atom(bub, bub)
h.wire(cut, [
  { node: atom, port: { kind: 'arg', index: 0 } },
  { node: c, port: { kind: 'output' } },
])
const d = h.build()

const canvas = document.getElementById('c') as HTMLCanvasElement
const ctx = canvas.getContext('2d')!
let state = initialState(d)

function frame(): void {
  canvas.width = window.innerWidth
  canvas.height = window.innerHeight
  for (let i = 0; i < 4; i++) state = step(d, state, DEFAULT_PARAMS)
  const scene = buildScene(d, state.positions)
  ctx.clearRect(0, 0, canvas.width, canvas.height)
  drawShapes(ctx, renderScene(scene), {
    scale: 6,
    offsetX: canvas.width / 2,
    offsetY: canvas.height / 2,
  })
  requestAnimationFrame(frame)
}
frame()
```

In `package.json`: add `"vite": "^6"` (or the major already present in the lockfile via vitest — match it) to `devDependencies` and `"demo": "vite demo"` to `scripts`. Run `npm install` after editing. Add `demo/dist` to `.gitignore` (create the file if absent) so the build output never lands in a commit.

- [ ] **Step 4: Verify PASS, full suite, typecheck.** Also run `npx vite build demo --logLevel error` once to prove the demo page compiles (do not start the dev server — it blocks). Run the vite build AFTER staging is decided and never `git add` `demo/dist`.

- [ ] **Step 5: Commit**

```bash
git add src/view/display.ts src/view/canvas.ts src/view/index.ts demo/index.html demo/main.ts package.json package-lock.json .gitignore
git commit -m "feat(view): display-list renderer, canvas adapter, vite demo page"
```

---

### Task 7: Whole-plan battery

**Files:**
- Test: `tests/view/pipeline.test.ts`

- [ ] **Step 1: Write the battery** (must pass against Tasks 1–6)

`tests/view/pipeline.test.ts`:

```ts
import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../src/kernel/term/parse'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { applyDoubleCutIntro } from '../../src/kernel/rules/doublecut'
import { mkSelection } from '../../src/kernel/diagram/subgraph/selection'
import { buildScene, initialState, settle, renderScene, DEFAULT_PARAMS } from '../../src/view/index'

const noConsts = new Set<string>()
const p = (s: string) => parseTerm(s, noConsts)

describe('the full pipeline tracks kernel edits', () => {
  it('renders before and after a rule application without carrying any state across', () => {
    const h = new DiagramBuilder()
    const n = h.termNode(h.root, p('\\x. x'))
    const d1 = h.build()
    const s1 = settle(d1, initialState(d1), DEFAULT_PARAMS, 20000)
    const shapes1 = renderScene(buildScene(d1, s1.positions))
    expect(shapes1.length).toBeGreaterThan(0)

    const sel = mkSelection(d1, { region: d1.root, regions: [], nodes: [n], wires: [] })
    const d2 = applyDoubleCutIntro(d1, sel)
    // fresh physics for the edited diagram — layout is never persisted
    const s2 = settle(d2, initialState(d2), DEFAULT_PARAMS, 20000)
    const shapes2 = renderScene(buildScene(d2, s2.positions))
    const circles2 = shapes2.filter((s) => s.kind === 'circle')
    expect(circles2).toHaveLength(2) // the two new cuts
    expect(circles2.filter((c) => c.kind === 'circle' && c.fill !== undefined)).toHaveLength(1)
  })

  it('scenes contain no NaN under extreme aspect terms', () => {
    const h = new DiagramBuilder()
    h.termNode(h.root, p('\\a. \\b. \\c. \\d. \\e. a (b (c (d e)))'))
    const d = h.build()
    const s = settle(d, initialState(d), DEFAULT_PARAMS, 20000)
    for (const shape of renderScene(buildScene(d, s.positions))) {
      expect(JSON.stringify(shape)).not.toContain('null') // NaN serializes to null
    }
  })
})
```

- [ ] **Step 2: Run; all must pass.** Any failure: investigate, fix test-first, report prominently.

- [ ] **Step 3: Commit**

```bash
git add tests/view/pipeline.test.ts
git commit -m "test(view): kernel-to-pixels pipeline battery"
```

---

## Completion criteria for this plan

- `npx vitest run` green, `npx tsc --noEmit` clean, `npx vite build demo` compiles.
- Demonstrated in tests: the layering check passes and would fail loudly on a kernel→view import; Tromp grids place binder bars by depth, app bars below the deeper side, rails per distinct port with drops at every occurrence, and never overlap bars on a row; the bend keeps all content inside the C, puts outermost binders outermost, pierces ports radially past the rim, and exits the output through the gap at angle 0; scenes enclose every node in its region circle with nesting respected, shade exactly the negative regions, and reject missing/unknown positions loudly; physics is deterministic, settles within budget (failing loudly when the budget is exhausted), separates sibling regions and coincident nodes; the display list paints regions→wires→nodes with stable golden-angle binder hues and finite coordinates; the pipeline re-renders kernel edits from fresh physics with no state carried across (layout never persisted, structurally).
- Plan 10 builds the interactive shell on `src/view/index.ts` + `src/kernel/proof/index.ts`.

## Carried obligations (forward)

- Plan 10: hybrid binder rendering's hover tethers; pin-while-dragging; canvas-first chrome; selection/cut/bubble creation UX (select then button/hotkey); formula and definition building flows; bundled examples (λ demos + Frege arithmetic); E2E tests; PiP/split companion target.
- Matcher symmetry/bare-wire items and the abstraction R(x,x) limitation (Plans 6–7) remain.
- Physics is O(n²) per tick (all-pairs); fine at proof scale, revisit with spatial hashing only if Plan 10 hits real lag.
