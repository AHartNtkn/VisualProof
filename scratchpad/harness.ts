// Shared measurement harness for Task 3 face-reachability re-measurement.
import { DiagramBuilder } from '../src/kernel/diagram/builder'
import { parseTerm } from '../src/kernel/term/parse'
import { relSig, TERM } from '../src/kernel/diagram/sig'
import type { Diagram } from '../src/kernel/diagram/diagram'
import { mkEngine, resolveLeg } from '../src/view/engine'
import type { Engine, WireView } from '../src/view/engine'
import { settleStep, totalEnergy, __decompose, recomputeRegions, establishFrame, resolveOverlaps } from '../src/view/relax'
import { __PROBE2 } from '../src/view/relax'
import { __PROBE } from '../src/view/engine'

export const MERGE_EPS = 0.01
const rel = (n: number) => relSig(Array.from({ length: n }, () => TERM))

/** N unary refs sharing one N-way wire (a pure interior junction). */
export function nWay(n: number): { d: Diagram } {
  const b = new DiagramBuilder()
  const refs = Array.from({ length: n }, (_, i) => b.ref(b.root, `r${i}`, rel(3)))
  b.wire(b.root, refs.map((r) => ({ node: r, port: { kind: 'arg' as const, index: 0 } })))
  return { d: b.build() }
}

/** A 3-bind ∀ wire: cut c1 ⊃ cut c2 with 3 term nodes in c2, one wire scoped at c1
    over their freeVars → binds=3 + via = 4 terminals → 2 branch vertices, 1 internal edge. */
export function forallVia3(): { d: Diagram } {
  const b = new DiagramBuilder()
  const c1 = b.cut(b.root)
  const c2 = b.cut(c1)
  const ns = ['p', 'q', 's'].map((nm) => b.termNode(c2, parseTerm(nm)))
  for (let i = 0; i < ns.length; i++) b.wire(c2, [{ node: ns[i]!, port: { kind: 'output' } }])
  b.wire(c1, ns.map((n, i) => ({ node: n, port: { kind: 'freeVar' as const, name: ['p', 'q', 's'][i]! } })))
  return { d: b.build() }
}

/** The one multi-terminal wire in an engine (the junction under test). */
export function junctionWire(e: Engine): WireView {
  let best: WireView | null = null
  for (const w of e.wires.values()) {
    const terms = w.binds.length + w.slots.length + (w.endBodyId ? 1 : 0)
    if (terms >= 4 && (best === null || terms > best.binds.length)) best = w
  }
  if (best === null) for (const w of e.wires.values()) if (w.branches.length > 0) best = w
  return best!
}

/** Pin the N ref bodies of an nWay wire at given positions, facing the centroid. */
export function pinAt(e: Engine, w: WireView, pos: readonly { x: number; y: number }[]): Set<string> {
  const pinned = new Set<string>()
  const cx = pos.reduce((s, p) => s + p.x, 0) / pos.length
  const cy = pos.reduce((s, p) => s + p.y, 0) / pos.length
  w.binds.forEach((bd, i) => {
    const b = e.bodies.get(bd.body)!
    b.pos = { ...pos[i]! }
    const la = b.localAnchor.get(bd.key)!
    b.theta = Math.atan2(cy - b.pos.y, cx - b.pos.x) - Math.atan2(la.y, la.x)
    pinned.add(bd.body)
  })
  return pinned
}

/** Internal (branch–branch) edges of a wire: [legIndex, bi, bj, ℓ_e]. */
export function internalEdges(w: WireView): { li: number; bi: number; bj: number; len: number }[] {
  const out: { li: number; bi: number; bj: number; len: number }[] = []
  w.legs.forEach((leg, li) => {
    if (leg.a.kind === 'branch' && leg.b.kind === 'branch') {
      const bi = leg.a.i, bj = leg.b.i
      const p = w.branches[bi]!, q = w.branches[bj]!
      out.push({ li, bi, bj, len: Math.hypot(p.x - q.x, p.y - q.y) })
    }
  })
  return out
}

export function minInternal(w: WireView): number {
  const es = internalEdges(w)
  return es.length === 0 ? Infinity : Math.min(...es.map((x) => x.len))
}

/** Topology signature: which terminals share EACH branch (directly attached), e.g. "01|23".
    Grouped per branch (NOT unioned across internal edges) so it identifies the pairing. */
export function topoSig(w: WireView): string {
  const per = new Map<number, number[]>()
  for (const leg of w.legs) {
    const term = leg.a.kind === 'bind' ? leg.a.i : leg.b.kind === 'bind' ? leg.b.i : (leg.a.kind === 'end' || leg.b.kind === 'end') ? 99 : -1
    const br = leg.a.kind === 'branch' ? leg.a.i : leg.b.kind === 'branch' ? leg.b.i : -1
    if (term < 0 || br < 0) continue
    const g = per.get(br) ?? []; g.push(term); per.set(br, g)
  }
  return [...per.values()].map((a) => a.sort((x, y) => x - y).join('')).sort().join('|')
}

export function resetProbes(): void {
  __PROBE2.teCalls = 0; __PROBE2.teMs = 0; __PROBE2.fcCalls = 0; __PROBE2.faceCross.length = 0
  __PROBE.resolveLegCalls = 0
}

export { totalEnergy, __decompose, settleStep, mkEngine, recomputeRegions, establishFrame, resolveOverlaps, resolveLeg, __PROBE2, __PROBE }
