import type { Diagram } from '../../kernel/diagram/diagram'
import type { ProofStep } from '../../kernel/proof/step'
import { applyStepAt } from '../../kernel/term/reduce'
import type { Term } from '../../kernel/term/term'
import { bendGrid, type NodeGeometry } from '../../view/bend'
import { ascaleOf, pkey, type Engine } from '../../view/engine'
import { mkGeomMorph, mkGridMorph } from '../../view/morph'
import type { Shape, Theme } from '../../view/paint'
import { trompGrid } from '../../view/tromp'
import type { Vec2 } from '../../view/vec'

export type MotionPreferences = {
  conversionAnimation: boolean
  connectedMorph: boolean
  speed: number
  transitionGhosts: boolean
  hoverEaseMs: 0 | 120
}

export function defaultMotionPreferences(reduced: boolean): MotionPreferences {
  return {
    conversionAnimation: !reduced,
    connectedMorph: true,
    speed: 1,
    transitionGhosts: !reduced,
    hoverEaseMs: reduced ? 0 : 120,
  }
}

export function setMotionSpeed(preferences: MotionPreferences, speed: number): void {
  const clamped = Math.max(0.25, Math.min(3, Number.isFinite(speed) ? speed : 1))
  preferences.speed = Math.round(clamped * 4) / 4
}

export function smoothstep(progress: number): number {
  const p = Math.max(0, Math.min(1, progress))
  return p * p * (3 - 2 * p)
}

type ConversionStep = Extract<ProofStep, { rule: 'conversion' }>

export function conversionFrames(diagram: Diagram, step: ConversionStep): readonly Term[] {
  const node = diagram.nodes[step.node]
  if (node === undefined || node.kind !== 'term') return []
  const frames: Term[] = [node.term]
  let left = node.term
  for (const reduction of step.certificate.leftSteps) {
    left = applyStepAt(left, reduction)
    frames.push(left)
  }
  const right: Term[] = [step.term]
  let target = step.term
  for (const reduction of step.certificate.rightSteps) {
    target = applyStepAt(target, reduction)
    right.push(target)
  }
  right.reverse()
  frames.push(...right.slice(1))
  return frames
}

export type MotionCoordinatorOptions = {
  preferences(): MotionPreferences
  diagram(): Diagram
  engine(): Engine
  theme(): Theme
}

export type MotionDebugState = {
  readonly playing: boolean
  readonly segment: number
  readonly progress: number
  readonly morph: 'connected' | 'pinned-v1' | null
  readonly ghosts: number
  readonly pulses: number
  readonly hover: number
}

type ActiveConversion = {
  readonly node: string
  readonly morphs: readonly ((progress: number) => NodeGeometry)[]
  readonly start: number
  readonly commit: () => void
  readonly kind: 'connected' | 'pinned-v1'
  segment: number
  progress: number
}

type Ghost = { readonly pos: Vec2; readonly discR: number; readonly start: number }
type Pulse = { readonly id: string; readonly start: number }

const GHOST_MS = 320
const PULSE_MS = 450
const STEP_MS = 520

const withAlpha = (color: string, alpha: number): string => {
  const byte = Math.max(0, Math.min(255, Math.round(alpha * 255))).toString(16).padStart(2, '0')
  return /^#[0-9a-f]{6}$/i.test(color) ? `${color}${byte}` : color
}

export class MotionCoordinator {
  #options: MotionCoordinatorOptions
  #active: ActiveConversion | null = null
  #ghosts: Ghost[] = []
  #pulses: Pulse[] = []
  #hoverKey: string | null = null
  #hoverSince = 0
  #disposed = false

  constructor(options: MotionCoordinatorOptions) {
    this.#options = options
  }

  get playing(): boolean { return this.#active !== null }

  run(step: ProofStep, preparedCommit: () => void, now: number): boolean {
    if (this.#disposed) return false
    const preferences = this.#options.preferences()
    if (step.rule !== 'conversion' || !preferences.conversionAnimation || this.#active !== null) {
      preparedCommit()
      return false
    }
    const frames = conversionFrames(this.#options.diagram(), step)
    if (frames.length <= 1) {
      preparedCommit()
      return false
    }
    const grids = frames.map(trompGrid)
    const connected = preferences.connectedMorph
    const morphs = grids.slice(1).map((grid, index) => connected
      ? mkGridMorph(grids[index]!, grid)
      : mkGeomMorph(bendGrid(grids[index]!), bendGrid(grid)))
    this.#active = {
      node: step.node,
      morphs,
      start: now,
      commit: preparedCommit,
      kind: connected ? 'connected' : 'pinned-v1',
      segment: 0,
      progress: 0,
    }
    return true
  }

  frame(now: number): void {
    const active = this.#active
    if (active === null || this.#disposed) return
    const stepMs = STEP_MS / this.#options.preferences().speed
    const elapsed = Math.max(0, now - active.start)
    const segment = Math.floor(elapsed / stepMs)
    if (segment >= active.morphs.length) {
      this.#active = null
      active.commit()
      return
    }
    const progress = smoothstep((elapsed - segment * stepMs) / stepMs)
    active.segment = segment
    active.progress = progress
    const geometry = active.morphs[segment]!(progress)
    const engine = this.#options.engine()
    const body = engine.bodies.get(active.node)
    if (body === undefined) return
    const scale = ascaleOf('term')
    const anchors = new Map(body.localAnchor)
    let anatomyR = 3
    const setAnchor = (key: string, point: Vec2): void => {
      const scaled = { x: point.x * scale, y: point.y * scale }
      anchors.set(key, scaled)
      anatomyR = Math.max(anatomyR, Math.hypot(scaled.x, scaled.y))
    }
    setAnchor(pkey({ kind: 'output' }), geometry.outputAnchor)
    for (const [name, point] of Object.entries(geometry.portAnchors)) {
      setAnchor(pkey({ kind: 'freeVar', name }), point)
    }
    for (const arc of geometry.arcs) anatomyR = Math.max(anatomyR, arc.r)
    engine.bodies.set(active.node, { ...body, geometry, localAnchor: anchors, discR: anatomyR + 2 })
  }

  observeSwap(before: Engine, after: Engine, now: number): void {
    if (!this.#options.preferences().transitionGhosts || this.#disposed) return
    for (const [id, body] of before.bodies) {
      if (!after.bodies.has(id)) this.#ghosts.push({ pos: { ...body.pos }, discR: body.discR * before.scale, start: now })
    }
    for (const id of after.bodies.keys()) {
      if (!before.bodies.has(id)) this.#pulses.push({ id, start: now })
    }
  }

  overlays(now: number): readonly Shape[] {
    if (this.#disposed) return []
    const theme = this.#options.theme()
    const shapes: Shape[] = []
    this.#ghosts = this.#ghosts.filter((ghost) => {
      const fraction = (now - ghost.start) / GHOST_MS
      if (fraction >= 1) return false
      shapes.push({
        kind: 'circle', center: ghost.pos, r: ghost.discR * (1 + Math.max(0, fraction) * 0.4),
        fill: withAlpha(theme.ink, (1 - Math.max(0, fraction)) * 0.34), stroke: null,
        width: 0, insetColor: null, glow: null,
      })
      return true
    })
    const engine = this.#options.engine()
    this.#pulses = this.#pulses.filter((pulse) => {
      const fraction = (now - pulse.start) / PULSE_MS
      const body = engine.bodies.get(pulse.id)
      if (fraction >= 1 || body === undefined) return false
      shapes.push({
        kind: 'circle', center: body.pos, r: body.discR * engine.scale + 2 + Math.max(0, fraction) * 6,
        fill: null, stroke: withAlpha(theme.interaction.valid, (1 - Math.max(0, fraction)) * 0.54),
        width: 1.8, insetColor: null, glow: null,
      })
      return true
    })
    return shapes
  }

  setHover(key: string | null, now: number): void {
    if (key === this.#hoverKey) return
    this.#hoverKey = key
    this.#hoverSince = now
  }

  hoverFraction(now: number): number {
    if (this.#hoverKey === null) return 0
    const duration = this.#options.preferences().hoverEaseMs
    return duration === 0 ? 1 : Math.max(0, Math.min(1, (now - this.#hoverSince) / duration))
  }

  debugState(now: number): MotionDebugState {
    return {
      playing: this.playing,
      segment: this.#active?.segment ?? -1,
      progress: this.#active?.progress ?? 0,
      morph: this.#active?.kind ?? null,
      ghosts: this.#ghosts.length,
      pulses: this.#pulses.length,
      hover: this.hoverFraction(now),
    }
  }

  cancel(): void {
    this.#active = null
    this.#ghosts = []
    this.#pulses = []
    this.#hoverKey = null
  }

  dispose(): void {
    this.cancel()
    this.#disposed = true
  }
}
