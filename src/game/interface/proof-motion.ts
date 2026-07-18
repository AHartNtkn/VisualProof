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

export type ProofMotionPreferences = {
  conversionAnimation: boolean
  connectedMorph: boolean
  speed: number
  transitionGhosts: boolean
  hoverEaseMs: 0 | 120
}

export const gameProofMotionPreferences = (reduced: boolean): ProofMotionPreferences => ({
  conversionAnimation: !reduced,
  connectedMorph: true,
  speed: 1,
  transitionGhosts: !reduced,
  hoverEaseMs: reduced ? 0 : 120,
})

type ConversionStep = Extract<ProofStep, { readonly rule: 'conversion' }>

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

export type ProofMotionDebug = {
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
const smoothstep = (progress: number): number => {
  const clamped = Math.max(0, Math.min(1, progress))
  return clamped * clamped * (3 - 2 * clamped)
}
const withAlpha = (color: string, alpha: number): string => {
  const byte = Math.max(0, Math.min(255, Math.round(alpha * 255))).toString(16).padStart(2, '0')
  return /^#[0-9a-f]{6}$/i.test(color) ? `${color}${byte}` : color
}

export class GameProofMotion {
  readonly #preferences: () => ProofMotionPreferences
  readonly #diagram: () => Diagram
  readonly #engine: () => Engine
  readonly #theme: () => Theme
  #active: ActiveConversion | null = null
  #ghosts: Ghost[] = []
  #pulses: Pulse[] = []
  #hoverKey: string | null = null
  #hoverSince = 0
  #disposed = false

  constructor(options: {
    readonly preferences: () => ProofMotionPreferences
    readonly diagram: () => Diagram
    readonly engine: () => Engine
    readonly theme: () => Theme
  }) {
    this.#preferences = options.preferences
    this.#diagram = options.diagram
    this.#engine = options.engine
    this.#theme = options.theme
  }

  get playing(): boolean { return this.#active !== null }

  run(step: ProofStep, preparedCommit: () => void, now: number): boolean {
    if (this.#disposed) return false
    const preferences = this.#preferences()
    if (step.rule !== 'conversion' || !preferences.conversionAnimation || this.#active !== null) {
      preparedCommit()
      return false
    }
    const frames = conversionFrames(this.#diagram(), step)
    if (frames.length <= 1) {
      preparedCommit()
      return false
    }
    const grids = frames.map(trompGrid)
    const morphs = grids.slice(1).map((grid, index) => preferences.connectedMorph
      ? mkGridMorph(grids[index]!, grid)
      : mkGeomMorph(bendGrid(grids[index]!), bendGrid(grid)))
    this.#active = {
      node: step.node,
      morphs,
      start: now,
      commit: preparedCommit,
      kind: preferences.connectedMorph ? 'connected' : 'pinned-v1',
      segment: 0,
      progress: 0,
    }
    return true
  }

  frame(now: number): void {
    const active = this.#active
    if (active === null || this.#disposed) return
    const stepMs = STEP_MS / this.#preferences().speed
    const elapsed = Math.max(0, now - active.start)
    const segment = Math.floor(elapsed / stepMs)
    if (segment >= active.morphs.length) {
      this.#active = null
      active.commit()
      return
    }
    active.segment = segment
    active.progress = smoothstep((elapsed - segment * stepMs) / stepMs)
    const geometry = active.morphs[segment]!(active.progress)
    const engine = this.#engine()
    const body = engine.bodies.get(active.node)
    if (body === undefined) return
    const scale = ascaleOf('term')
    const anchors = new Map(body.localAnchor)
    let anatomyR = 3
    const anchor = (key: string, point: Vec2): void => {
      const scaled = { x: point.x * scale, y: point.y * scale }
      anchors.set(key, scaled)
      anatomyR = Math.max(anatomyR, Math.hypot(scaled.x, scaled.y))
    }
    anchor(pkey({ kind: 'output' }), geometry.outputAnchor)
    for (const [name, point] of Object.entries(geometry.portAnchors)) anchor(pkey({ kind: 'freeVar', name }), point)
    for (const arc of geometry.arcs) anatomyR = Math.max(anatomyR, arc.r)
    engine.bodies.set(active.node, { ...body, geometry, localAnchor: anchors, discR: anatomyR + 2 })
  }

  observeSwap(before: Engine, after: Engine, now: number): void {
    if (!this.#preferences().transitionGhosts || this.#disposed) return
    for (const [id, body] of before.bodies) {
      if (!after.bodies.has(id)) this.#ghosts.push({ pos: { ...body.pos }, discR: body.discR * before.scale, start: now })
    }
    for (const id of after.bodies.keys()) if (!before.bodies.has(id)) this.#pulses.push({ id, start: now })
  }

  overlays(now: number): readonly Shape[] {
    if (this.#disposed) return []
    const theme = this.#theme()
    const shapes: Shape[] = []
    this.#ghosts = this.#ghosts.filter((ghost) => {
      const progress = (now - ghost.start) / GHOST_MS
      if (progress >= 1) return false
      shapes.push({
        kind: 'circle', center: ghost.pos, r: ghost.discR * (1 + Math.max(0, progress) * 0.4),
        fill: withAlpha(theme.ink, (1 - Math.max(0, progress)) * 0.34), stroke: null,
        width: 0, insetColor: null, glow: null,
      })
      return true
    })
    const engine = this.#engine()
    this.#pulses = this.#pulses.filter((pulse) => {
      const progress = (now - pulse.start) / PULSE_MS
      const body = engine.bodies.get(pulse.id)
      if (progress >= 1 || body === undefined) return false
      shapes.push({
        kind: 'circle', center: body.pos,
        r: body.discR * engine.scale + 2 + Math.max(0, progress) * 6,
        fill: null, stroke: withAlpha(theme.interaction.valid, (1 - Math.max(0, progress)) * 0.54),
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
    const duration = this.#preferences().hoverEaseMs
    return duration === 0 ? 1 : Math.max(0, Math.min(1, (now - this.#hoverSince) / duration))
  }

  debug(now: number): ProofMotionDebug {
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

  dispose(): void {
    this.#active = null
    this.#ghosts = []
    this.#pulses = []
    this.#hoverKey = null
    this.#disposed = true
  }
}
