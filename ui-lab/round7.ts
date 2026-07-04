/**
 * ROUND 7 — MOTION, on the full winner stack (minimal chrome + scrubber).
 * Every motion layer is view-only (layer law) and individually toggleable:
 *  - βη ANIMATION (the user's design): converting a → b plays a's reduction
 *    to the common reduct a′, then b's reduction REVERSED (a → a′ → b), one
 *    readable step at a time; speed slider; off = instant (today).
 *  - TRANSITION GHOSTS: erased bodies fade out where they died; fresh bodies
 *    pulse a ring — moves show WHERE they acted instead of teleporting.
 *  - HOVER EASE: the hover tint fades in instead of snapping.
 */
import { boot, emptyStart, motionPrefs } from './shared'
import { mkChromeApp, installMinimalChrome } from './chrome'
import { installScrubber } from './history'
import { applyStepAt } from '../src/kernel/term/reduce'
import { trompGrid } from '../src/view/tromp'
import { bendGrid, type NodeGeometry } from '../src/view/bend'
import { anchorOf, ascaleOf, localToWorld, pkey } from '../src/view/engine'
import { freePorts, type Term } from '../src/kernel/term/term'
import type { Port } from '../src/kernel/diagram/diagram'
import type { ProofStep } from '../src/kernel/proof/step'
import type { Vec2 } from '../src/view/vec'

boot('Round 7 — motion', 'βη conversion ANIMATES (a → a′ → b, speed under ⚙); erasures fade out, fresh bodies pulse; hover eases — every layer toggleable', (lab) => {
  const motion = { convAnim: true, speed: 1, ghosts: true }
  motionPrefs.hoverEaseMs = 120

  // ---- βη playback: the node's anatomy DISSOLVES between the certificate's
  // reduction states while its port anchors LERP — wires read anchors live,
  // so they glide with the morph instead of disconnecting. rAF-driven,
  // smoothstep-eased, view-only; the real step commits after the last frame.
  let playing = false
  type Stage = { geom: NodeGeometry; anchors: Map<string, Vec2>; discR: number }
  const stageOf = (t: Term): Stage => {
    const geom = bendGrid(trompGrid(t))
    const anchors = new Map<string, Vec2>()
    const ascale = ascaleOf('term')
    let anatomyR = 3
    const ports: Port[] = [{ kind: 'output' }, ...freePorts(t).map((name): Port => ({ kind: 'freeVar', name }))]
    for (const port of ports) {
      const a0 = anchorOf(geom, { x: 0, y: 0 }, port)
      const a = { x: a0.x * ascale, y: a0.y * ascale }
      anchors.set(pkey(port), a)
      anatomyR = Math.max(anatomyR, Math.hypot(a.x, a.y))
    }
    for (const arc of geom.arcs) anatomyR = Math.max(anatomyR, arc.r)
    return { geom, anchors, discR: anatomyR + 2 }
  }
  let play: { nodeId: string; stages: Stage[]; oldGeom: NodeGeometry; alpha: number } | null = null
  const playConversion = (step: Extract<ProofStep, { rule: 'conversion' }>, commit: () => void): void => {
    const node = lab.d.nodes[step.node]
    if (node === undefined || node.kind !== 'term') { commit(); return }
    const frames: Term[] = [node.term]
    let t = node.term
    for (const s of step.certificate.leftSteps) { t = applyStepAt(t, s); frames.push(t) }
    const right: Term[] = [step.term]
    let u = step.term
    for (const s of step.certificate.rightSteps) { u = applyStepAt(u, s); right.push(u) }
    right.reverse() // a′ … b
    frames.push(...right.slice(1))
    if (frames.length <= 1) { commit(); return }
    playing = true
    const stages = frames.map(stageOf)
    play = { nodeId: step.node, stages, oldGeom: stages[0]!.geom, alpha: 0 }
    const t0 = performance.now()
    const smooth = (p: number): number => p * p * (3 - 2 * p) // C¹ ease
    const lerp = (a: Vec2, b2: Vec2, f: number): Vec2 => ({ x: a.x + (b2.x - a.x) * f, y: a.y + (b2.y - a.y) * f })
    const driver = () => {
      if (play === null) return
      const stepMs = 520 / motion.speed
      const el = performance.now() - t0
      const k = Math.floor(el / stepMs)
      if (k >= stages.length - 1) {
        play = null
        playing = false
        commit()
        lab.toast(`converted — played ${frames.length - 1} reduction step(s)`)
        return
      }
      const p = smooth((el - k * stepMs) / stepMs)
      const from = stages[k]!, to = stages[k + 1]!
      const b = lab.engine.bodies.get(step.node)
      if (b !== undefined) {
        // anchors: lerp shared keys; dying keys hold (they fade with the old
        // arcs); new keys sit at their destination — wires follow live
        const anchors = new Map(b.localAnchor)
        for (const [key, av] of from.anchors) {
          const bv = to.anchors.get(key)
          anchors.set(key, bv === undefined ? av : lerp(av, bv, p))
        }
        for (const [key, bv] of to.anchors) if (!from.anchors.has(key)) anchors.set(key, bv)
        lab.engine.bodies.set(step.node, {
          ...b,
          geometry: to.geom,
          localAnchor: anchors,
          discR: from.discR + (to.discR - from.discR) * p,
        })
      }
      play.oldGeom = from.geom
      play.alpha = 1 - p
      requestAnimationFrame(driver)
    }
    lab.toast('playing the evaluation…')
    requestAnimationFrame(driver)
  }
  // the outgoing state's anatomy dissolves over the incoming one
  lab.overlay((out) => {
    if (play === null) return
    const b = lab.engine.bodies.get(play.nodeId)
    if (b === undefined) return
    const a = Math.max(0, Math.min(1, play.alpha))
    const hex = Math.round(a * 0xb0).toString(16).padStart(2, '0')
    const stroke = `#1c2a33${hex}`
    const ascale = ascaleOf('term')
    for (const arc of play.oldGeom.arcs) {
      out.push({ kind: 'arc', center: b.pos, r: arc.r * ascale, a0: arc.a0 + b.theta, a1: arc.a1 + b.theta, stroke, width: 0.9, glow: null })
    }
    for (const r of play.oldGeom.radials) {
      out.push({
        kind: 'segment',
        from: localToWorld(b, { x: Math.cos(r.angle) * r.r0, y: Math.sin(r.angle) * r.r0 }),
        to: localToWorld(b, { x: Math.cos(r.angle) * r.r1, y: Math.sin(r.angle) * r.r1 }),
        stroke, width: 0.9, glow: null,
      })
    }
  })
  // input holds while the evaluation plays — it is a look, not a state
  const guard = (e: Event) => { if (playing) { e.stopImmediatePropagation(); e.preventDefault() } }
  lab.canvas.addEventListener('pointerdown', guard, { capture: true })
  window.addEventListener('keydown', guard, { capture: true })

  const app = mkChromeApp(lab, {
    interceptStep: (step, commit) => {
      if (motion.convAnim && step.rule === 'conversion') { playConversion(step, commit); return true }
      return false
    },
  })
  installMinimalChrome(lab, app)
  installScrubber(lab, app)

  // ---- transition ghosts + born pulses ----
  type Ghost = { pos: Vec2; discR: number; t0: number }
  const ghosts: Ghost[] = []
  const pulses: { id: string; t0: number }[] = []
  lab.onMutate((died, born) => {
    if (!motion.ghosts) return
    const now = performance.now()
    for (const d of died) ghosts.push({ ...d, t0: now })
    for (const id of born) pulses.push({ id, t0: now })
  })
  const GHOST_MS = 320, PULSE_MS = 450
  lab.overlay((out) => {
    const now = performance.now()
    for (let i = ghosts.length - 1; i >= 0; i--) {
      const g = ghosts[i]!
      const f = (now - g.t0) / GHOST_MS
      if (f >= 1) { ghosts.splice(i, 1); continue }
      const a = Math.round((1 - f) * 0x55).toString(16).padStart(2, '0')
      out.push({ kind: 'circle', center: g.pos, r: g.discR * (1 + f * 0.4), fill: `#57534e${a}`, stroke: null, width: 0, insetColor: null, glow: null })
    }
    for (let i = pulses.length - 1; i >= 0; i--) {
      const p = pulses[i]!
      const f = (now - p.t0) / PULSE_MS
      const b = lab.engine.bodies.get(p.id)
      if (f >= 1 || b === undefined) { pulses.splice(i, 1); continue }
      const a = Math.round((1 - f) * 0x88).toString(16).padStart(2, '0')
      out.push({ kind: 'circle', center: b.pos, r: b.discR + 2 + f * 6, fill: null, stroke: `#16a34a${a}`, width: 1.8, insetColor: null, glow: null })
    }
  })

  // ---- the motion panel (⚙): each layer toggleable, speed slider ----
  const panel = document.createElement('div')
  panel.style.cssText = 'position:fixed;right:8px;top:40px;z-index:7;font:12px system-ui;background:#ffffffee;border:1px solid #ccc;border-radius:8px;padding:8px 10px;display:flex;flex-direction:column;gap:6px'
  const row = (label: string, initial: boolean, onFlip: (on: boolean) => void): void => {
    const l = document.createElement('label')
    l.style.cssText = 'display:flex;gap:6px;align-items:center;cursor:pointer'
    const cb = document.createElement('input')
    cb.type = 'checkbox'
    cb.checked = initial
    cb.addEventListener('change', () => onFlip(cb.checked))
    l.append(cb, label)
    panel.append(l)
  }
  panel.append(Object.assign(document.createElement('div'), { textContent: '⚙ motion', style: 'color:#999;font-size:11px;text-transform:uppercase' }))
  row('βη animation', motion.convAnim, (on) => { motion.convAnim = on })
  const speedRow = document.createElement('label')
  speedRow.style.cssText = 'display:flex;gap:6px;align-items:center'
  const slider = document.createElement('input')
  slider.type = 'range'
  slider.min = '0.25'; slider.max = '3'; slider.step = '0.25'; slider.value = '1'
  slider.style.width = '90px'
  const speedLabel = document.createElement('span')
  speedLabel.textContent = '1×'
  slider.addEventListener('input', () => { motion.speed = Number(slider.value); speedLabel.textContent = `${slider.value}×` })
  speedRow.append('speed', slider, speedLabel)
  panel.append(speedRow)
  row('transition ghosts', motion.ghosts, (on) => { motion.ghosts = on })
  row('hover ease', true, (on) => { motionPrefs.hoverEaseMs = on ? 120 : 0 })
  document.body.append(panel)
}, emptyStart)
