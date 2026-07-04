/**
 * Round-1 lab scaffold: one showcase diagram + the real render pipeline +
 * per-variant interaction hooks. Each variant page supplies ONLY its
 * selection/hover mechanic; everything painted comes from src/view verbatim.
 */
import { parseTerm } from '../src/kernel/term/parse'
import { DiagramBuilder } from '../src/kernel/diagram/builder'
import type { Diagram, DiagramNode, Endpoint, NodeId, Region, RegionId, Wire, WireId } from '../src/kernel/diagram/diagram'
import { mkDiagram, portKey } from '../src/kernel/diagram/diagram'
import { freshId } from '../src/kernel/diagram/subgraph/freshId'
import { joinPorts } from '../src/app/edit'
import { carryOver, mkEngine, pkey, type Engine, type Leg } from '../src/view/engine'
import type { Vec2 } from '../src/view/vec'
import { settleStep } from '../src/view/relax'
import { paint, LIGHT, type Shape, type Theme } from '../src/view/paint'
import { drawShapes } from '../src/view/canvas'
import { computeLegs, hobbyBezier, legPaths, boundaryExits, existentialStubs, type ExStub, type LegGeom, type WirePath } from '../src/view/wires'
import { buildSelection, dragTarget, hitTest, type Hit } from '../src/app/hittest'
import { addBubble, addCut, addRefNode, addTermNode, deleteSelection } from '../src/app/edit'
import { mkSelection } from '../src/kernel/diagram/subgraph/selection'
import { deepestCommonAncestor, polarity } from '../src/kernel/diagram/regions'

const p = (s: string) => parseTerm(s)

/** Nested cuts, a bubble with two atoms, terms, a 3-way junction, boundary. */
export function showcase(): { d: Diagram; boundary: WireId[] } {
  const b = new DiagramBuilder()
  const t1 = b.termNode(b.root, p('\\x. \\y. x (x y)'))
  const t2 = b.termNode(b.root, p('f g'))
  const w3 = b.wire(b.root, [
    { node: t1, port: { kind: 'output' } },
    { node: t2, port: { kind: 'freeVar', name: 'f' } },
    { node: t2, port: { kind: 'freeVar', name: 'g' } },
  ])
  void w3
  const cut = b.cut(b.root)
  const t3 = b.termNode(cut, p('\\z. z'))
  const inner = b.cut(cut)
  const bub = b.bubble(inner, 1)
  const a1 = b.atom(bub, bub)
  const a2 = b.atom(bub, bub)
  b.wire(bub, [
    { node: a1, port: { kind: 'arg', index: 0 } },
    { node: a2, port: { kind: 'arg', index: 0 } },
  ])
  const wb = b.wire(b.root, [{ node: t2, port: { kind: 'output' } }])
  const wb2 = b.wire(b.root, [{ node: t3, port: { kind: 'output' } }])
  // one genuine loose end (∃ stub) so end-pulling gestures have a handle
  const t4 = b.termNode(b.root, p('\\w. w w'))
  b.wire(b.root, [{ node: t4, port: { kind: 'output' } }])
  return { d: b.build(), boundary: [wb, wb2] }
}

/** An empty sheet — the true entry experience for chrome pages. */
export function emptyStart(): { d: Diagram; boundary: WireId[] } {
  return { d: new DiagramBuilder().build(), boundary: [] }
}

/** Round-7 motion preferences (view-only, never semantic — layer law).
    Pages toggle these; the shared layers read them live. */
export const motionPrefs = {
  /** Hover tint ease-in duration (ms); 0 = instant (today's behavior). */
  hoverEaseMs: 0,
}

export type LabCtx = {
  engine: Engine
  d: Diagram
  boundary: WireId[]
  canvas: HTMLCanvasElement
  view: { scale: number; offsetX: number; offsetY: number }
  toWorld(sx: number, sy: number): { x: number; y: number }
  hitAt(sx: number, sy: number): Hit | null
  /** Everything inside a region subtree (for subtree selection variants). */
  subtreeHits(r: RegionId): Hit[]
  polarityOf(r: RegionId): 'positive' | 'negative'
  /** Register a per-frame overlay: shapes appended after the base paint (additive). */
  overlay(fn: (out: Shape[]) => void): void
  /** Register per-frame chrome work (HTML positioning, enablement) — runs
      before painting, never contributes shapes. */
  onFrame(fn: () => void): void
  describe(h: Hit | null): string
  /** Swap in a mutated diagram: pushes undo history, filters the boundary to
      surviving wires (or replaces it when `boundary` is given — session side
      switches), rebuilds the engine warm (carryOver), optionally pins a fresh
      node at a world point so creation lands under the cursor. */
  mutate(next: Diagram, place?: { node: NodeId; at: Vec2 }, boundary?: readonly WireId[]): void
  undo(): boolean
  /** What Ctrl+Z would restore (the memory box renders this), or null. */
  peekUndo(): { d: Diagram; boundary: WireId[] } | null
  /** Deepest region whose circle contains the point (root when none does). */
  regionAt(w: Vec2): RegionId
  legs(): LegGeom[]
  /** Loose ends (∃ stubs) of the current layout. */
  stubs(): ExStub[]
  /** The diagram endpoint at one end of a leg (null at a junction end). */
  legEndpoint(leg: Leg, end: 'from' | 'to'): Endpoint | null
  /** Nearest leg within tolerance of a world point. */
  legAt(w: Vec2, tol?: number): LegGeom | null
  /** Nearest wire within tolerance, measured against EVERY stroke it draws —
      internal legs, boundary exits, and stubs (legAt sees only legs). */
  wireNear(w: Vec2, tol: number): WireId | null
  /** Legs whose strokes cross the world segment a–b. */
  legsCrossing(a: Vec2, b: Vec2): LegGeom[]
  /** Drop selection entries whose ids no longer exist. */
  prune(hs: Hit[]): Hit[]
  toast(text: string): void
  /** Pause/resume settling — while placing something, the world holds still. */
  freeze(on: boolean): void
  /** Observe diagram swaps (motion layers): dying bodies' last geometry and
      the ids born in the new engine. View-only. */
  onMutate(fn: (died: { pos: Vec2; discR: number }[], born: string[]) => void): void
}

export function boot(title: string, blurb: string, run: (ctx: LabCtx) => void, mk: () => { d: Diagram; boundary: WireId[] } = showcase, opts?: { wires?: (e: Engine, st: Theme) => Shape[] }): void {
  document.title = title
  const head = document.createElement('div')
  head.style.cssText = 'position:fixed;top:0;left:0;right:0;padding:8px 12px;background:#ffffffd8;font:13px system-ui;z-index:5;border-bottom:1px solid #ccc'
  head.innerHTML = `<b>${title}</b> — ${blurb} <span id="readout" style="float:right;color:#555"></span>`
  document.body.append(head)
  const canvas = document.createElement('canvas')
  canvas.style.cssText = 'position:fixed;inset:0'
  document.body.append(canvas)
  document.body.style.background = LIGHT.canvas
  const msg = document.createElement('div')
  msg.style.cssText = 'position:fixed;bottom:0;left:0;right:0;padding:6px 12px;background:#ffffffd8;font:13px system-ui;z-index:5;border-top:1px solid #ccc;color:#7c2d12;min-height:1.2em'
  document.body.append(msg)
  const ctx2d = canvas.getContext('2d')!
  const start = mk()
  const view = { scale: 6, offsetX: 0, offsetY: 0 }
  const history: { d: Diagram; boundary: WireId[] }[] = []
  const fit = () => {
    const sheet = lab.engine.regions.get(lab.d.root)
    const R = Math.max(sheet?.radius ?? 10, 10)
    const cx = sheet?.center.x ?? 0, cy = sheet?.center.y ?? 0
    view.scale = Math.min(6, (0.42 * Math.min(canvas.width, canvas.height)) / R)
    view.offsetX = canvas.width / 2 - cx * view.scale
    view.offsetY = canvas.height / 2 - cy * view.scale
  }
  const toWorld = (sx: number, sy: number) => ({ x: (sx - view.offsetX) / view.scale, y: (sy - view.offsetY) / view.scale })
  const overlays: ((out: Shape[]) => void)[] = []
  const frameHooks: (() => void)[] = []
  let frozen = false
  const mutateHooks: ((died: { pos: Vec2; discR: number }[], born: string[]) => void)[] = []
  const swap = (d2: Diagram, boundary2: WireId[]): void => {
    const next = mkEngine(d2, boundary2)
    carryOver(lab.engine, next)
    settleStep(next) // paint requires a settled engine — same discipline as the shell
    const died: { pos: Vec2; discR: number }[] = []
    for (const [id, b] of lab.engine.bodies) if (!next.bodies.has(id) && b.kind !== 'anchor') died.push({ pos: b.pos, discR: b.discR })
    const born: string[] = []
    for (const id of next.bodies.keys()) if (!lab.engine.bodies.has(id)) born.push(id)
    lab.d = d2
    lab.boundary = boundary2
    lab.engine = next
    for (const fn of mutateHooks) fn(died, born)
  }
  const lab: LabCtx = {
    engine: mkEngine(start.d, start.boundary), d: start.d, boundary: start.boundary, canvas, view, toWorld,
    hitAt: (sx, sy) => { const w = toWorld(sx, sy); return hitTest(lab.engine, w) },
    subtreeHits: (r) => {
      const out: Hit[] = [{ kind: 'region', id: r }]
      const walk = (rr: RegionId) => {
        for (const [id, reg] of Object.entries(lab.d.regions)) {
          if (reg.kind !== 'sheet' && reg.parent === rr) { out.push({ kind: 'region', id }); walk(id) }
        }
        for (const [id, n] of Object.entries(lab.d.nodes)) if (n.region === rr) out.push({ kind: 'node', id })
        for (const [id, w] of Object.entries(lab.d.wires)) if (w.scope === rr) out.push({ kind: 'wire', id })
      }
      walk(r)
      return out
    },
    polarityOf: (r) => polarity(lab.d, r),
    overlay: (fn) => { overlays.push(fn) },
    onFrame: (fn) => { frameHooks.push(fn) },
    describe: (h) => {
      if (h === null) return ''
      if (h.kind === 'node') { const n = lab.d.nodes[h.id]!; return n.kind === 'term' ? 'λ-term node' : n.kind === 'ref' ? `relation '${(n as { defId: string }).defId}'` : 'predicate atom' }
      if (h.kind === 'region') { const r = lab.d.regions[h.id]!; return `${r.kind === 'cut' ? 'cut' : 'bubble'} (${polarity(lab.d, h.id)})` }
      return 'line of identity'
    },
    mutate: (next, place, boundary) => {
      history.push({ d: lab.d, boundary: lab.boundary })
      swap(next, boundary !== undefined ? [...boundary] : lab.boundary.filter((w) => next.wires[w] !== undefined))
      if (place) {
        const b = lab.engine.bodies.get(place.node)
        if (b) { b.pos.x = place.at.x; b.pos.y = place.at.y }
      }
    },
    undo: () => {
      const prev = history.pop()
      if (prev === undefined) return false
      swap(prev.d, prev.boundary)
      return true
    },
    peekUndo: () => history.length === 0 ? null : history[history.length - 1]!,
    regionAt: (w) => {
      let best: { id: RegionId; radius: number } | null = null
      for (const [rid, g] of lab.engine.regions) {
        if (lab.d.regions[rid]!.kind === 'sheet') continue
        if (Math.hypot(w.x - g.center.x, w.y - g.center.y) <= g.radius && (best === null || g.radius < best.radius)) {
          best = { id: rid, radius: g.radius }
        }
      }
      return best === null ? lab.d.root : best.id
    },
    legs: () => computeLegs(lab.engine),
    stubs: () => existentialStubs(lab.engine),
    legEndpoint: (leg, end) => {
      const { body, key } = end === 'from' ? leg.from : leg.to
      if (lab.d.nodes[body] === undefined) return null
      const ep = lab.d.wires[leg.wid]?.endpoints.find((x) => x.node === body && pkey(x.port) === key)
      return ep ?? null
    },
    legAt: (w, tol = 2.5) => {
      let best: { g: LegGeom; dist: number } | null = null
      for (const g of computeLegs(lab.engine)) {
        const dist = pathDistance(w, hobbyBezier(g.pa, g.ta, g.pb, g.tb))
        if (dist <= tol && (best === null || dist < best.dist)) best = { g, dist }
      }
      return best?.g ?? null
    },
    wireNear: (w, tol) => {
      let best: { wid: WireId; dist: number } | null = null
      const consider = (wid: WireId, dist: number) => {
        if (dist <= tol && (best === null || dist < best.dist)) best = { wid, dist }
      }
      for (const g of computeLegs(lab.engine)) consider(g.leg.wid, pathDistance(w, hobbyBezier(g.pa, g.ta, g.pb, g.tb)))
      for (const x of boundaryExits(lab.engine)) consider(x.wid, pathDistance(w, x.path))
      for (const s of existentialStubs(lab.engine)) {
        consider(s.wid, Math.min(Math.hypot(w.x - s.from.x, w.y - s.from.y), Math.hypot(w.x - s.to.x, w.y - s.to.y)))
      }
      return best === null ? null : (best as { wid: WireId }).wid
    },
    legsCrossing: (a, b) => {
      const out: LegGeom[] = []
      for (const g of computeLegs(lab.engine)) {
        const pts = samplePath(hobbyBezier(g.pa, g.ta, g.pb, g.tb))
        for (let i = 0; i + 1 < pts.length; i++) {
          if (segmentsIntersect(a, b, pts[i]!, pts[i + 1]!)) { out.push(g); break }
        }
      }
      return out
    },
    prune: (hs) => hs.filter((h) =>
      h.kind === 'node' ? lab.d.nodes[h.id] !== undefined
      : h.kind === 'region' ? lab.d.regions[h.id] !== undefined
      : lab.d.wires[h.id] !== undefined),
    toast: (text) => { msg.textContent = text },
    freeze: (on) => { frozen = on },
    onMutate: (fn) => { mutateHooks.push(fn) },
  }
  const frame = () => {
    if (canvas.width !== innerWidth || canvas.height !== innerHeight) { canvas.width = innerWidth; canvas.height = innerHeight }
    if (!frozen) for (let i = 0; i < 4; i++) settleStep(lab.engine)
    fit()
    for (const fn of frameHooks) fn()
    const shapes: Shape[] = [...paint(lab.engine, LIGHT, opts?.wires)]
    for (const fn of overlays) fn(shapes)
    ctx2d.clearRect(0, 0, canvas.width, canvas.height)
    drawShapes(ctx2d, shapes, view)
    requestAnimationFrame(frame)
  }
  ;(window as unknown as { __lab: LabCtx }).__lab = lab
  run(lab)
  requestAnimationFrame(frame)
}

// ---- path geometry (sampling mirrors hittest's tolerance approach) ----

function samplePath(p: WirePath, n = 16): Vec2[] {
  const out: Vec2[] = []
  for (let i = 0; i <= n; i++) {
    const t = i / n, u = 1 - t
    out.push({
      x: u * u * u * p.from.x + 3 * u * u * t * p.c1.x + 3 * u * t * t * p.c2.x + t * t * t * p.to.x,
      y: u * u * u * p.from.y + 3 * u * u * t * p.c1.y + 3 * u * t * t * p.c2.y + t * t * t * p.to.y,
    })
  }
  return out
}

function pathDistance(w: Vec2, p: WirePath): number {
  let best = Infinity
  for (const q of samplePath(p)) best = Math.min(best, Math.hypot(w.x - q.x, w.y - q.y))
  return best
}

function segmentsIntersect(a: Vec2, b: Vec2, c: Vec2, d: Vec2): boolean {
  const cross = (o: Vec2, p: Vec2, q: Vec2) => (p.x - o.x) * (q.y - o.y) - (p.y - o.y) * (q.x - o.x)
  const d1 = cross(a, b, c), d2 = cross(a, b, d), d3 = cross(c, d, a), d4 = cross(c, d, b)
  return d1 * d2 < 0 && d3 * d4 < 0
}

export function pointInPolygon(w: Vec2, poly: readonly Vec2[]): boolean {
  let inside = false
  for (let i = 0, j = poly.length - 1; i < poly.length; j = i++) {
    const a = poly[i]!, b = poly[j]!
    if (a.y > w.y !== b.y > w.y && w.x < ((b.x - a.x) * (w.y - a.y)) / (b.y - a.y) + a.x) inside = !inside
  }
  return inside
}

/** The Round-1 verdict selection: brush painting with hover that never goes
    silent. Installs pointer handlers + overlay; returns live handles. Other
    gestures claim a pointerdown first via `claim` (checked before brushing). */
export function installBrush(lab: LabCtx, claim?: (h: Hit | null, e: PointerEvent) => boolean, active: () => boolean = () => true): {
  selected: Hit[]
  isSelected(h: Hit | null): boolean
  clear(): void
  prune(): void
  hover(): Hit | null
} {
  let hover: Hit | null = null
  const selected: Hit[] = []
  let brushing = false
  let brushErase = false
  let fromVoid = false
  let painted = false
  const isSelected = (h: Hit | null) => h !== null && selected.some((s) => sameHit(s, h))
  const applyBrush = (h: Hit | null) => {
    if (h === null) return
    const i = selected.findIndex((s) => sameHit(s, h))
    if (brushErase) { if (i >= 0) { selected.splice(i, 1); painted = true } }
    else if (i < 0) { selected.push(h); painted = true }
  }
  const announce = () => readout(hover ? lab.describe(hover) + (isSelected(hover) ? ' — selected' : '') : '')
  // USER ruling: the MOVING brush (de)selects a region only when the stroke
  // passes over its drawn ring — sweeping through the interior must not grab
  // the cut. The ring is a drawn stroke, so it picks like one (the wire
  // tolerance). A plain CLICK keeps whole-disc selection.
  const paintable = (h: Hit | null, w: Vec2): Hit | null => {
    if (h === null || h.kind !== 'region') return h
    const g = lab.engine.regions.get(h.id)
    if (g === undefined) return h
    return Math.abs(Math.hypot(w.x - g.center.x, w.y - g.center.y) - g.radius) <= 1.5 ? h : null
  }
  // Ctrl+drag = physics-only handle (USER ruling, round 4): pull any body
  // against the live simulation; no proof or diagram meaning whatsoever.
  let physDrag: { id: string; cursor: Vec2 } | null = null
  lab.onFrame(() => {
    if (physDrag === null) return
    const b = lab.engine.bodies.get(physDrag.id)
    if (b) { b.pos = { x: physDrag.cursor.x, y: physDrag.cursor.y }; b.vel = { x: 0, y: 0 } }
  })
  lab.canvas.addEventListener('pointermove', (e) => {
    if (physDrag) { physDrag.cursor = lab.toWorld(e.clientX, e.clientY); return }
    if (!active()) return
    hover = lab.hitAt(e.clientX, e.clientY)
    if (brushing) applyBrush(paintable(hover, lab.toWorld(e.clientX, e.clientY)))
    announce()
  })
  lab.canvas.addEventListener('pointerup', () => { physDrag = null })
  lab.canvas.addEventListener('pointerdown', (e) => {
    // Ctrl+drag physics is mode-independent (it means nothing, everywhere)
    if (e.ctrlKey && e.button === 0) {
      const w = lab.toWorld(e.clientX, e.clientY)
      const t = dragTarget(lab.engine, w)
      if (t?.kind === 'body') physDrag = { id: t.id, cursor: w }
      return
    }
    if (!active()) return
    const h = lab.hitAt(e.clientX, e.clientY)
    if (claim && claim(h, e)) return
    brushing = true
    painted = false
    fromVoid = h === null
    // a stroke starting in the void PAINTS (adds) whatever it passes over;
    // only a stroke that never touches anything clears (the still empty click)
    brushErase = h !== null && isSelected(h)
    applyBrush(h)
    announce()
  })
  lab.canvas.addEventListener('pointerup', () => {
    if (brushing && fromVoid && !painted) { selected.length = 0; announce() }
    brushing = false
  })
  const tint = (h: Hit, color: string, out: Shape[]) => {
    if (h.kind === 'node') {
      const b = lab.engine.bodies.get(h.id)
      if (b) out.push({ kind: 'circle', center: b.pos, r: b.discR, fill: color, stroke: null, width: 0, insetColor: null, glow: null })
    } else if (h.kind === 'region') {
      const g = lab.engine.regions.get(h.id)
      if (g) out.push({ kind: 'circle', center: g.center, r: g.radius, fill: color, stroke: null, width: 0, insetColor: null, glow: null })
    }
  }
  let hoverSince = 0
  let lastHoverKey = ''
  lab.overlay((out) => {
    if (!active()) return
    for (const s of selected) out.push(...hitShapes(lab, s, '#d97706', 2.5))
    if (hover === null) { lastHoverKey = ''; return }
    const key = `${hover.kind}:${hover.id}`
    if (key !== lastHoverKey) { lastHoverKey = key; hoverSince = performance.now() }
    // motion pref: the tint eases in instead of snapping (E3)
    const f = motionPrefs.hoverEaseMs > 0 ? Math.min(1, (performance.now() - hoverSince) / motionPrefs.hoverEaseMs) : 1
    const a2 = (base: number): string => Math.round(base * f).toString(16).padStart(2, '0')
    if (isSelected(hover)) {
      out.push(...hitShapes(lab, hover, '#92400e', 3.4))
      tint(hover, `#92400e${a2(0x26)}`, out)
    } else {
      out.push(...hitShapes(lab, hover, '#2563eb', 1.8))
      tint(hover, `#2563eb${a2(0x1c)}`, out)
    }
  })
  ;(window as unknown as { __labSel: Hit[] }).__labSel = selected
  return {
    selected, isSelected,
    clear: () => { selected.length = 0 },
    prune: () => { const kept = lab.prune(selected); selected.length = 0; selected.push(...kept) },
    hover: () => hover,
  }
}

// ---- construction surgery the app lacks at edit level ----

/** Detach one endpoint of a wire into its own singleton wire (scope kept —
    the original scope is an ancestor of every endpoint, so both halves stay
    valid and no quantifier moves). */
export function severEndpoint(d: Diagram, wid: WireId, ep: Endpoint): Diagram {
  const w = d.wires[wid]
  if (w === undefined) throw new Error(`unknown wire '${wid}'`)
  const rest = w.endpoints.filter((x) => !(x.node === ep.node && portKey(x.port) === portKey(ep.port)))
  if (rest.length === w.endpoints.length) throw new Error(`endpoint is not on wire '${wid}'`)
  if (rest.length === 0) throw new Error('a single loose end cannot be severed further')
  const nw = freshId(new Set(Object.keys(d.wires)), 'w')
  return mkDiagramFrom(d, {
    ...d.wires,
    [wid]: { scope: w.scope, endpoints: rest },
    [nw]: { scope: w.scope, endpoints: [ep] },
  })
}

/** Merge two wires into one (identify the individuals), scoped at the deepest
    common scope — the construction-level join the shell button performs. */
export function mergeWires(d: Diagram, wa: WireId, wb: WireId): Diagram {
  if (wa === wb) throw new Error('a wire is already joined to itself')
  const a = d.wires[wa], b = d.wires[wb]
  if (a === undefined || b === undefined) throw new Error('unknown wire')
  const ea = a.endpoints[0], eb = b.endpoints[0]
  if (ea === undefined || eb === undefined) throw new Error('wire has no endpoints to join through')
  return joinPorts(d, ea, eb)
}

function mkDiagramFrom(d: Diagram, wires: Record<WireId, { scope: RegionId; endpoints: readonly Endpoint[] }>): Diagram {
  return mkDiagram({ root: d.root, regions: { ...d.regions }, nodes: { ...d.nodes }, wires })
}

export type BrushHandle = ReturnType<typeof installBrush>

/** Run an edit; kernel refusals land in the toast (the refusal IS the UX copy). */
export function tryEdit(lab: LabCtx, fn: () => void): boolean {
  try { fn(); return true } catch (e) { lab.toast(e instanceof Error ? e.message : String(e)); return false }
}

/** Wrap hit items in a cut (arity null) or bubble. Unlike the app's wrap,
    wires now living wholly inside the new region are rescoped INTO it — a
    wire left at the parent is quantified outside the cut, which is not what
    drawing a circle around it says. */
export function wrapHits(lab: LabCtx, hits: readonly Hit[], arity: number | null): RegionId {
  const sel = buildSelection(lab.d, hits)
  const res = arity === null ? addCut(lab.d, sel) : addBubble(lab.d, sel, arity)
  const inSub = (r: RegionId): boolean => {
    let cur = r
    for (;;) {
      if (cur === res.region) return true
      const reg = res.diagram.regions[cur]!
      if (reg.kind === 'sheet') return false
      cur = reg.parent
    }
  }
  const wires: Record<WireId, { scope: RegionId; endpoints: readonly Endpoint[] }> = {}
  for (const [id, w] of Object.entries(res.diagram.wires)) {
    const moves = w.scope === sel.region && w.endpoints.length > 0
      && w.endpoints.every((ep) => inSub(res.diagram.nodes[ep.node]!.region))
    wires[id] = moves ? { scope: res.region, endpoints: w.endpoints } : w
  }
  lab.mutate(mkDiagramFrom(res.diagram, wires))
  return res.region
}

/** An empty cut as a child of `region` (variant-c radial "cut here"). */
export function emptyCutAt(lab: LabCtx, region: RegionId, at: Vec2): RegionId {
  const sel = mkSelection(lab.d, { region, regions: [], nodes: [], wires: [] })
  const res = addCut(lab.d, sel)
  lab.mutate(res.diagram)
  const g = lab.engine.regions.get(res.region)
  if (g) { g.center.x = at.x; g.center.y = at.y }
  return res.region
}

export function spawnTermAt(lab: LabCtx, region: RegionId, src: string, at: Vec2): void {
  const { diagram, node } = addTermNode(lab.d, region, parseTerm(src))
  lab.mutate(diagram, { node, at })
}

export const REL_PALETTE = [
  { name: 'zero', arity: 1 },
  { name: 'succ', arity: 2 },
  { name: 'plus', arity: 3 },
  { name: 'nat', arity: 1 },
] as const

export function spawnRelAt(lab: LabCtx, region: RegionId, name: string, arity: number, at: Vec2): void {
  const { diagram, node } = addRefNode(lab.d, region, name, arity)
  lab.mutate(diagram, { node, at })
}

/** Ctrl+Z undo and Delete/Backspace on the brush selection — every Round-2
    page carries these identically (A4/A10 baseline). */
export function installEditKeys(lab: LabCtx, brush: BrushHandle, active: () => boolean = () => true): void {
  window.addEventListener('keydown', (e) => {
    if (!active()) return
    if (document.activeElement instanceof HTMLInputElement) return
    if ((e.ctrlKey || e.metaKey) && e.key === 'z') {
      e.preventDefault()
      if (lab.undo()) { brush.prune(); lab.toast('undo') } else lab.toast('nothing to undo')
    } else if (e.key === 'Delete' || e.key === 'Backspace') {
      if (brush.selected.length === 0) { lab.toast('nothing selected to delete'); return }
      tryEdit(lab, () => {
        lab.mutate(deleteHits(lab.d, brush.selected))
        brush.clear()
        lab.toast('deleted (selected boundaries dissolve; their contents propagate up)')
      })
    }
  })
}

/** Inline one-line input at a screen point. `commit` returns true to close;
    returning false (e.g. a parse refusal already toasted) keeps it open. */
export function promptAt(sx: number, sy: number, placeholder: string, commit: (text: string) => boolean): void {
  const inp = document.createElement('input')
  inp.placeholder = placeholder
  inp.style.cssText = `position:fixed;left:${sx}px;top:${sy}px;z-index:8;font:13px system-ui;padding:3px 8px;border:1.5px solid #d97706;border-radius:5px;outline:none;background:#fff;width:14rem`
  document.body.append(inp)
  let closed = false
  const close = () => { if (!closed) { closed = true; inp.remove() } }
  inp.addEventListener('keydown', (e) => {
    e.stopPropagation()
    if (e.key === 'Enter') { if (commit(inp.value)) close() }
    else if (e.key === 'Escape') close()
  })
  inp.addEventListener('blur', close)
  setTimeout(() => inp.focus(), 0)
}

/** Stroke shape for one leg (strand) of a wire. */
export function legShape(g: LegGeom, stroke: string, width: number): Shape {
  const p = hobbyBezier(g.pa, g.ta, g.pb, g.tb)
  return { kind: 'bezier', from: p.from, c1: p.c1, c2: p.c2, to: p.to, stroke, width, glow: null }
}

/** Merge every listed wire into one (N-ary join — selecting three lines and
    joining should not take two gestures). */
export function mergeAllWires(d: Diagram, wids: readonly WireId[]): Diagram {
  if (wids.length < 2) throw new Error(`joining needs at least two lines, got ${wids.length}`)
  let cur = d
  for (let i = 1; i < wids.length; i++) cur = mergeWires(cur, wids[0]!, wids[i]!)
  return cur
}

function subtreeContains(d: Diagram, root: RegionId, r: RegionId): boolean {
  let cur = r
  for (;;) {
    if (cur === root) return true
    const reg = d.regions[cur]
    if (reg === undefined || reg.kind === 'sheet') return false
    cur = reg.parent
  }
}

/** Absorb hits that already live inside a selected region's subtree: picking
    a cut AND something within it means the subtree, once — not a refusal. */
export function absorbHits(d: Diagram, hits: readonly Hit[]): Hit[] {
  const roots = hits.filter((h) => h.kind === 'region').map((h) => h.id)
  const strictlyInside = (r: RegionId): boolean => roots.some((root) => r !== root && subtreeContains(d, root, r))
  const insideOrOn = (r: RegionId): boolean => roots.some((root) => subtreeContains(d, root, r))
  return hits.filter((h) =>
    h.kind === 'region' ? !strictlyInside(h.id)
    : h.kind === 'node' ? !insideOrOn(d.nodes[h.id]!.region)
    : !insideOrOn(d.wires[h.id]!.scope))
}

/** Remove a cut/bubble boundary, splicing its contents into the parent. */
export function dissolveRegion(d: Diagram, rid: RegionId): Diagram {
  const r = d.regions[rid]
  if (r === undefined) throw new Error(`unknown region '${rid}'`)
  if (r.kind === 'sheet') throw new Error('the sheet cannot be dissolved')
  const parent = r.parent
  const regions: Record<RegionId, Region> = {}
  for (const [id, reg] of Object.entries(d.regions)) {
    if (id === rid) continue
    regions[id] = reg.kind !== 'sheet' && reg.parent === rid
      ? (reg.kind === 'cut' ? { kind: 'cut', parent } : { kind: 'bubble', parent, arity: reg.arity })
      : reg
  }
  const nodes: Record<NodeId, DiagramNode> = {}
  for (const [id, n] of Object.entries(d.nodes)) {
    nodes[id] = n.region === rid
      ? (n.kind === 'term' ? { kind: 'term', region: parent, term: n.term }
        : n.kind === 'atom' ? { kind: 'atom', region: parent, binder: n.binder }
        : { kind: 'ref', region: parent, defId: n.defId, arity: n.arity })
      : n
  }
  const wires: Record<WireId, Wire> = {}
  for (const [id, w] of Object.entries(d.wires)) {
    wires[id] = w.scope === rid ? { scope: parent, endpoints: w.endpoints } : w
  }
  return mkDiagram({ root: d.root, regions, nodes, wires })
}

/** Wires whose EVERY endpoint sits on the given nodes would survive a
    deletion as bare ∃ dots — semantically an equivalence (closed terms
    denote, so ∃x.⊤ ≡ ⊤) and pure clutter (USER ruling): deletions take
    them along. */
export function orphanedWires(d: Diagram, nodeIds: ReadonlySet<NodeId>): WireId[] {
  return Object.entries(d.wires)
    .filter(([, w]) => w.endpoints.length > 0 && w.endpoints.every((ep) => nodeIds.has(ep.node)))
    .map(([id]) => id)
}

/** Delete hit items. Nodes/wires go (grouped by region — spanning several
    regions is fine); selected cuts/bubbles DISSOLVE: the boundary vanishes
    and unselected contents propagate to the parent. Wires that would be
    left with no endpoints are deleted along (USER ruling). */
export function deleteHits(d: Diagram, hits: readonly Hit[]): Diagram {
  let cur = d
  // take along wires that only connect to deleted nodes (no bare ∃ litter)
  const deadNodes = new Set(hits.filter((h) => h.kind === 'node').map((h) => h.id))
  const extra: Hit[] = orphanedWires(d, deadNodes)
    .filter((w) => !hits.some((h) => h.kind === 'wire' && h.id === w))
    .map((w): Hit => ({ kind: 'wire', id: w }))
  hits = [...hits, ...extra]
  const groups = new Map<RegionId, Hit[]>()
  for (const h of hits) {
    if (h.kind === 'region') continue
    const anchor = h.kind === 'node' ? cur.nodes[h.id]?.region : cur.wires[h.id]?.scope
    if (anchor === undefined) throw new Error(`unknown ${h.kind} '${h.id}'`)
    const g = groups.get(anchor) ?? []
    g.push(h)
    groups.set(anchor, g)
  }
  for (const g of groups.values()) cur = deleteSelection(cur, buildSelection(cur, g))
  const depth = (r: RegionId): number => {
    let n = 0, c = r
    for (;;) {
      const reg = cur.regions[c]!
      if (reg.kind === 'sheet') return n
      n++; c = reg.parent
    }
  }
  const rs = hits.filter((h) => h.kind === 'region').map((h) => h.id).sort((a, b) => depth(b) - depth(a))
  for (const rid of rs) cur = dissolveRegion(cur, rid)
  return cur
}

/** Move a node into another region. Wires wholly owned by the node travel
    with it; shared wires keep their scope when still valid, else correct to
    the deepest common ancestor of their endpoints (the tightest valid scope). */
export function reparentNode(d: Diagram, nid: NodeId, region: RegionId): Diagram {
  const n = d.nodes[nid]
  if (n === undefined) throw new Error(`unknown node '${nid}'`)
  if (d.regions[region] === undefined) throw new Error(`unknown region '${region}'`)
  if (n.region === region) return d
  const nodes: Record<NodeId, DiagramNode> = {
    ...d.nodes,
    [nid]: n.kind === 'term' ? { kind: 'term', region, term: n.term }
      : n.kind === 'atom' ? { kind: 'atom', region, binder: n.binder }
      : { kind: 'ref', region, defId: n.defId, arity: n.arity },
  }
  const regionOf = (id: NodeId): RegionId => nodes[id]!.region
  const wires: Record<WireId, Wire> = {}
  for (const [id, w] of Object.entries(d.wires)) {
    if (!w.endpoints.some((ep) => ep.node === nid)) { wires[id] = w; continue }
    if (w.endpoints.every((ep) => ep.node === nid)) { wires[id] = { scope: region, endpoints: w.endpoints }; continue }
    const stillValid = w.endpoints.every((ep) => subtreeContains(d, w.scope, regionOf(ep.node)))
    const scope = stillValid ? w.scope : w.endpoints.map((ep) => regionOf(ep.node)).reduce((a, b) => deepestCommonAncestor(d, a, b))
    wires[id] = { scope, endpoints: w.endpoints }
  }
  return mkDiagram({ root: d.root, regions: { ...d.regions }, nodes, wires })
}

/** Detach the node-side endpoint of a leg into its own wire (the sever a
    scissors stroke or strand double-click performs). */
export function severLeg(lab: LabCtx, g: LegGeom): boolean {
  const ep = lab.legEndpoint(g.leg, 'to') ?? lab.legEndpoint(g.leg, 'from')
  if (ep === null) { lab.toast('that strand runs between junctions; sever nearer a port'); return false }
  return tryEdit(lab, () => { lab.mutate(severEndpoint(lab.d, g.leg.wid, ep)) })
}

/** Ring/stroke overlays for a hit, in the given color. */
export function hitShapes(lab: LabCtx, h: Hit, stroke: string, width = 2.5): Shape[] {
  const e = lab.engine
  if (h.kind === 'node') {
    const b = e.bodies.get(h.id)
    return b === undefined ? [] : [{ kind: 'circle', center: b.pos, r: b.discR, fill: null, stroke, width, insetColor: null, glow: null }]
  }
  if (h.kind === 'region') {
    const g = e.regions.get(h.id)
    return g === undefined ? [] : [{ kind: 'circle', center: g.center, r: g.radius, fill: null, stroke, width, insetColor: null, glow: null }]
  }
  const out: Shape[] = []
  for (const l of legPaths(e)) if (l.wid === h.id) out.push({ kind: 'bezier', from: l.path.from, c1: l.path.c1, c2: l.path.c2, to: l.path.to, stroke, width: width + 0.5, glow: null })
  for (const x of boundaryExits(e)) if (x.wid === h.id) out.push({ kind: 'bezier', from: x.path.from, c1: x.path.c1, c2: x.path.c2, to: x.path.to, stroke, width: width + 0.5, glow: null })
  for (const s of existentialStubs(e)) if (s.wid === h.id) out.push({ kind: 'segment', from: s.from, to: s.to, stroke, width: width + 0.5, glow: null })
  return out
}

export function sameHit(a: Hit | null, b: Hit | null): boolean {
  return a !== null && b !== null && a.kind === b.kind && a.id === b.id
}

export function readout(text: string): void {
  const el = document.getElementById('readout')
  if (el) el.textContent = text
}
