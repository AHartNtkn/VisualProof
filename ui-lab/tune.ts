/**
 * WIRE-PHYSICS TUNING BOARD (plan 21 feel pass). Every live constant of the
 * physics on a slider, three scenarios, a kick button, and a copy button
 * that prints the current values — dial the feel in, then hand the numbers
 * back. All parameters are the REAL engine parameters (WIREP / PACE), so
 * what you feel here is exactly what ships.
 */
import { boot, labPace, type LabCtx } from './shared'
import { mkMultiportStart, installDrag } from './multiport'
import { WIREP } from '../src/view/wirechain'
import { PACE } from '../src/view/relax'
import { DiagramBuilder } from '../src/kernel/diagram/builder'
import type { Diagram, WireId } from '../src/kernel/diagram/diagram'
import { parseTerm } from '../src/kernel/term/parse'

function dangleScenario(): { d: Diagram; boundary: WireId[] } {
  const b = new DiagramBuilder()
  b.ref(b.root, 'plus', 3)
  b.ref(b.root, 'nat', 1)
  const s = b.ref(b.root, 'succ', 2)
  const t = b.termNode(b.root, parseTerm('\\x. f x'))
  b.wire(b.root, [
    { node: s, port: { kind: 'arg', index: 0 } },
    { node: t, port: { kind: 'freeVar', name: 'f' } },
  ])
  return { d: b.build(), boundary: [] }
}

function forallScenario(): { d: Diagram; boundary: WireId[] } {
  const b = new DiagramBuilder()
  const cut = b.cut(b.root)
  const lt = b.ref(cut, 'lt', 2)
  const gt = b.ref(cut, 'gt', 2)
  b.wire(b.root, [
    { node: lt, port: { kind: 'arg', index: 0 } },
    { node: gt, port: { kind: 'arg', index: 0 } },
  ])
  b.ref(b.root, 'zero', 1)
  const t = b.termNode(b.root, parseTerm('\\x. x'))
  b.wire(b.root, [
    { node: gt, port: { kind: 'arg', index: 1 } },
    { node: t, port: { kind: 'output' } },
  ])
  return { d: b.build(), boundary: [] }
}

type Knob = {
  label: string
  obj: Record<string, number>
  key: string
  min: number
  max: number
  step: number
}

boot('Wire-physics tuning board', 'every live constant on a slider — dial the feel, then COPY VALUES and report the numbers; drag nodes / kick to test settling', (lab: LabCtx) => {
  installDrag(lab)
  ;(window as unknown as { __tune: { WIREP: typeof WIREP; PACE: typeof PACE } }).__tune = { WIREP, PACE }

  const defaults = new Map<string, number>()
  const knobs: (Knob | string)[] = [
    'WIRE',
    { label: 'tension (wants short)', obj: WIREP, key: 'tension', min: 0.2, max: 8, step: 0.1 },
    { label: 'bend (wants straight)', obj: WIREP, key: 'bend', min: 0, max: 1.5, step: 0.05 },
    { label: 'barrier (pushes discs)', obj: WIREP, key: 'barrierSlope', min: 0, max: 20, step: 0.5 },
    { label: 'clearance margin', obj: WIREP, key: 'clearanceMargin', min: 0, max: 5, step: 0.25 },
    { label: 'wire speed cap', obj: WIREP, key: 'travelCap', min: 0.1, max: 1.5, step: 0.05 },
    'PACING',
    { label: 'wire step (responsiveness)', obj: PACE, key: 'chainStep', min: 0.02, max: 0.8, step: 0.01 },
    { label: '∃-dot step', obj: PACE, key: 'homedStep', min: 0.01, max: 0.4, step: 0.01 },
    { label: 'body timestep', obj: PACE, key: 'dt', min: 0.02, max: 0.15, step: 0.005 },
    { label: 'body damping (syrup)', obj: PACE, key: 'damp', min: 1, max: 10, step: 0.25 },
    { label: 'rotation drag', obj: PACE, key: 'rotDrag', min: 0.3, max: 4, step: 0.1 },
    { label: 'ticks per frame', obj: labPace as unknown as Record<string, number>, key: 'ticksPerFrame', min: 1, max: 12, step: 1 },
    'CONTENT',
    { label: 'anchoring scale', obj: PACE, key: 'softScale', min: 8, max: 36, step: 1 },
    { label: 'sibling gap', obj: PACE, key: 'sibGap', min: 2, max: 12, step: 0.5 },
    { label: 'disc repulsion', obj: PACE, key: 'rep', min: 300, max: 2000, step: 50 },
    'SCOPE (∃/∀ tips)',
    { label: 'ring strength', obj: PACE, key: 'ringSlope', min: 2, max: 20, step: 1 },
    { label: 'ring band', obj: PACE, key: 'ringBand', min: 1, max: 10, step: 0.5 },
  ]

  const panel = document.createElement('div')
  panel.style.cssText = 'position:fixed;right:8px;top:40px;bottom:40px;width:280px;overflow-y:auto;z-index:7;font:12px system-ui;background:#ffffffee;border:1px solid #ccc;border-radius:8px;padding:10px'
  const sliders: { knob: Knob; input: HTMLInputElement; readout: HTMLSpanElement }[] = []
  for (const item of knobs) {
    if (typeof item === 'string') {
      const h = document.createElement('div')
      h.textContent = item
      h.style.cssText = 'color:#999;font-size:10px;text-transform:uppercase;margin:10px 0 2px'
      panel.append(h)
      continue
    }
    defaults.set(`${item.key}`, item.obj[item.key]!)
    const row = document.createElement('div')
    row.style.cssText = 'display:flex;align-items:center;gap:6px;margin:2px 0'
    const label = document.createElement('span')
    label.textContent = item.label
    label.style.cssText = 'flex:1'
    const input = document.createElement('input')
    input.type = 'range'
    input.min = String(item.min)
    input.max = String(item.max)
    input.step = String(item.step)
    input.value = String(item.obj[item.key])
    input.style.width = '90px'
    const readout = document.createElement('span')
    readout.textContent = String(item.obj[item.key])
    readout.style.cssText = 'width:38px;text-align:right;font-variant-numeric:tabular-nums'
    input.addEventListener('input', () => {
      item.obj[item.key] = Number(input.value)
      readout.textContent = input.value
    })
    row.append(label, input, readout)
    panel.append(row)
    sliders.push({ knob: item, input, readout })
  }

  // ---- action row ----
  const actions = document.createElement('div')
  actions.style.cssText = 'display:flex;flex-wrap:wrap;gap:4px;margin-top:10px'
  const btn = (text: string, fn: () => void): void => {
    const b = document.createElement('button')
    b.textContent = text
    b.style.cssText = 'font:12px system-ui;padding:3px 8px;border:1px solid #999;border-radius:6px;background:#fff;cursor:pointer'
    b.addEventListener('click', fn)
    actions.append(b)
  }
  const scenarios: Record<string, () => { d: Diagram; boundary: WireId[] }> = {
    showcase: mkMultiportStart,
    dangles: dangleScenario,
    '∀+cut': forallScenario,
  }
  for (const [name, mk] of Object.entries(scenarios)) {
    btn(name, () => {
      const s = mk()
      lab.mutate(s.d, undefined, s.boundary)
      lab.toast(`scenario: ${name}`)
    })
  }
  btn('kick', () => {
    let i = 0
    for (const b of lab.engine.bodies.values()) {
      // deterministic scatter (golden-angle spiral) — physics-only
      const a = i * 2.399963
      b.pos = { x: Math.cos(a) * (10 + 6 * i), y: Math.sin(a) * (10 + 6 * i) }
      b.vel = { x: 0, y: 0 }
      i++
    }
    lab.toast('kicked — watch it settle')
  })
  btn('reset values', () => {
    for (const s of sliders) {
      const d = defaults.get(s.knob.key)!
      s.knob.obj[s.knob.key] = d
      s.input.value = String(d)
      s.readout.textContent = String(d)
    }
    lab.toast('defaults restored')
  })
  btn('copy values', () => {
    const dump: Record<string, number> = {}
    for (const s of sliders) dump[s.knob.key] = s.knob.obj[s.knob.key]!
    const json = JSON.stringify(dump, null, 2)
    console.log('TUNED VALUES:', json)
    void navigator.clipboard?.writeText(json)
    lab.toast('values copied to clipboard (and console)')
  })
  panel.append(actions)

  // ---- live stats ----
  const stats = document.createElement('div')
  stats.style.cssText = 'margin-top:8px;color:#666;font-variant-numeric:tabular-nums'
  panel.append(stats)
  let prev: Map<string, { x: number; y: number }> = new Map()
  let calm = 0
  lab.onFrame(() => {
    let maxV = 0
    for (const [id, b] of lab.engine.bodies) {
      const p = prev.get(id)
      if (p !== undefined) maxV = Math.max(maxV, Math.hypot(b.pos.x - p.x, b.pos.y - p.y))
      prev.set(id, { x: b.pos.x, y: b.pos.y })
    }
    calm = maxV < 0.01 ? calm + 1 : 0
    stats.textContent = `max body speed ${maxV.toFixed(3)}/frame · ${calm > 30 ? 'SETTLED' : 'settling…'}`
  })

  document.body.append(panel)
  lab.toast('drag nodes, kick, switch scenarios — tune until it feels right, then COPY VALUES')
}, mkMultiportStart)
