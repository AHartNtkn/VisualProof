/**
 * Junction gallery renderer (uncommitted deliverable for the user's VISUAL RULING on
 * the freed-tangent + restructuring junctions). Builds each scene, settles it through
 * the real mkEngine + settle pipeline, paints it with the LIGHT theme, and serializes
 * the emitted Shape[] verbatim to SVG — no hand-drawing. Run: `npx tsx
 * scripts/render-junction-gallery.ts`. Output: .superpowers/sdd/junction-gallery/*.svg
 */
import { mkdirSync, writeFileSync } from 'node:fs'
import { DiagramBuilder } from '../src/kernel/diagram/builder'
import { relSig, TERM } from '../src/kernel/diagram/sig'
import type { Diagram, WireId } from '../src/kernel/diagram/diagram'
import { mkEngine, frameBounds } from '../src/view/engine'
import type { Engine } from '../src/view/engine'
import { settle, settleStep } from '../src/view/relax'
import { paint, LIGHT, type Shape } from '../src/view/paint'
import type { Vec2 } from '../src/view/vec'
import { mkReplay } from '../src/app/replay'
import { bootFixture } from '../tests/app/boot-fixture'

const rel = (n: number) => relSig(Array.from({ length: n }, () => TERM))
const OUT = '.superpowers/sdd/junction-gallery'

// ---- SVG serialization of the painted Shape[] (world coordinates) ----
const f = (n: number): string => (Math.round(n * 100) / 100).toString()
function arcPts(cx: number, cy: number, r: number, a0: number, a1: number): Vec2[] {
  const out: Vec2[] = []
  const n = Math.max(2, Math.ceil((Math.abs(a1 - a0) / (2 * Math.PI)) * 48))
  for (let i = 0; i <= n; i++) { const a = a0 + (a1 - a0) * (i / n); out.push({ x: cx + Math.cos(a) * r, y: cy + Math.sin(a) * r }) }
  return out
}
function poly(pts: readonly Vec2[], stroke: string, w: number): string {
  return `<polyline points="${pts.map((p) => `${f(p.x)},${f(p.y)}`).join(' ')}" fill="none" stroke="${stroke}" stroke-width="${f(w)}" stroke-linejoin="round" stroke-linecap="round"/>`
}
function shapeToSvg(s: Shape): string {
  switch (s.kind) {
    case 'frame': return `<rect x="${f(s.x)}" y="${f(s.y)}" width="${f(s.w)}" height="${f(s.h)}" rx="${f(s.cornerW)}" fill="${s.fill}" stroke="${s.stroke}" stroke-width="${f(s.width)}"/>`
    case 'circle': {
      const parts = [`<circle cx="${f(s.center.x)}" cy="${f(s.center.y)}" r="${f(s.r)}" fill="${s.fill ?? 'none'}"${s.stroke !== null ? ` stroke="${s.stroke}" stroke-width="${f(s.width)}"` : ''}/>`]
      return parts.join('')
    }
    case 'arc': return poly(arcPts(s.center.x, s.center.y, s.r, s.a0, s.a1), s.stroke, s.width)
    case 'segment': return poly([s.from, s.to], s.stroke, s.width)
    case 'polyline': return poly(s.pts, s.stroke, s.width)
    case 'stub': return poly([s.from, s.to], s.stroke, s.width) + `<circle cx="${f(s.dot.x)}" cy="${f(s.dot.y)}" r="${f(s.dotRpx * 0.5)}" fill="${s.stroke}"/>`
    case 'dot': return `<circle cx="${f(s.center.x)}" cy="${f(s.center.y)}" r="${f(s.rPx * 0.5)}" fill="${s.fill}"/>`
    case 'label': return `<text x="${f(s.center.x)}" y="${f(s.center.y)}" font-family="${s.font}" font-size="${f(Math.max(3, s.r * 0.5))}" font-weight="600" fill="${s.color}" text-anchor="middle" dominant-baseline="central">${s.text.replace(/[<>&]/g, (c) => ({ '<': '&lt;', '>': '&gt;', '&': '&amp;' }[c]!))}</text>`
  }
}
function renderSvg(e: Engine): string {
  const shapes = paint(e, LIGHT)
  const fb = frameBounds(e)!
  const pad = 8
  const vb = `${f(fb.minX - pad)} ${f(fb.minY - pad)} ${f(fb.maxX - fb.minX + 2 * pad)} ${f(fb.maxY - fb.minY + 2 * pad)}`
  const body = shapes.map(shapeToSvg).join('\n  ')
  return `<svg xmlns="http://www.w3.org/2000/svg" viewBox="${vb}" width="640" height="640">\n  <rect x="${f(fb.minX - pad)}" y="${f(fb.minY - pad)}" width="${f(fb.maxX - fb.minX + 2 * pad)}" height="${f(fb.maxY - fb.minY + 2 * pad)}" fill="#f4f1ea"/>\n  ${body}\n</svg>\n`
}

// ---- scenes ----
function symTriple(): Diagram {
  const b = new DiagramBuilder()
  const r = [b.ref(b.root, 'p', rel(1)), b.ref(b.root, 'q', rel(1)), b.ref(b.root, 's', rel(1))]
  b.wire(b.root, r.map((n) => ({ node: n, port: { kind: 'arg' as const, index: 0 } })))
  return b.build()
}
function fourWaySym(): Diagram {
  const b = new DiagramBuilder()
  const r = [b.ref(b.root, 'a', rel(2)), b.ref(b.root, 'bb', rel(2)), b.ref(b.root, 'cc', rel(2)), b.ref(b.root, 'dd', rel(2))]
  b.wire(b.root, r.map((n) => ({ node: n, port: { kind: 'arg' as const, index: 0 } })))
  return b.build()
}

/** Settle a free scene to its fixed point. */
function settled(d: Diagram, boundary: WireId[] = []): Engine {
  const e = mkEngine(d, boundary)
  settle(e, 8000)
  return e
}
/** Pin the ref nodes at given world positions and settle around them (frame refit). */
function settledPinned(d: Diagram, corners: readonly Vec2[]): Engine {
  const e = mkEngine(d, [])
  settle(e, 1)
  const ids = [...e.bodies.values()].filter((x) => x.kind === 'ref').map((x) => x.id)
  ids.forEach((id, n) => { if (corners[n]) { const b = e.bodies.get(id)!; b.pos = { ...corners[n]! }; b.theta = 0 } })
  e.frame = null
  const pinned = new Set(ids)
  for (let t = 0; t < 6000; t++) { if (!settleStep(e, pinned)) break }
  return e
}

async function main(): Promise<void> {
  mkdirSync(OUT, { recursive: true })
  const write = (name: string, e: Engine): void => { writeFileSync(`${OUT}/${name}.svg`, renderSvg(e)); console.log(`wrote ${OUT}/${name}.svg`) }

  // 1. symmetric 3-way (free)
  write('symmetric-3way', settled(symTriple()))
  // 2. asymmetric 3-way: one distant terminal
  write('asymmetric-3way', settledPinned(symTriple(), [{ x: -22, y: -10 }, { x: -22, y: 12 }, { x: 46, y: 1 }]))
  // 3. collinear-ish 3-way: three terminals nearly in a line
  write('collinear-3way', settledPinned(symTriple(), [{ x: -40, y: -2 }, { x: 0, y: 2 }, { x: 40, y: -2 }]))
  // 4. symmetric 4-way (free)
  write('symmetric-4way', settled(fourWaySym()))
  // 5. rectangle 4-way (post-restructuring): terminals at a wide rectangle's corners
  write('rectangle-4way', settledPinned(fourWaySym(), [{ x: -40, y: -12 }, { x: -40, y: 12 }, { x: 40, y: -12 }, { x: 40, y: 12 }]))
  // 6. a real mid-proof frege step with multi-attachment wires
  const ctx = (await bootFixture()).ctx
  const r = mkReplay('plusComm', ctx)
  const k = Math.floor(r.actionCount / 2)
  const eR = mkEngine(r.diagramAt(k), r.boundaryAt(k))
  settle(eR, 4000)
  write(`frege-plusComm-step${k}`, eR)
  console.log('gallery complete')
}
main().catch((err) => { console.error(err); process.exit(1) })
