import type { Engine } from '../../view/engine'
import {
  planBetaMotion,
  sampleBetaMotion,
  type LambdaMotionPlan,
  type LambdaStrokeFrame,
} from '../../view/lambda-motion'
import type { Shape, Theme } from '../../view/paint'
import type { ReductionStep } from '../../kernel/term/reduce'
import type { Term } from '../../kernel/term/term'
import type { Vec2 } from '../../view/vec'

export type MotionPreferences = {
  speed: number
  transitionGhosts: boolean
  hoverEaseMs: 0 | 120
}

export function defaultMotionPreferences(reduced: boolean): MotionPreferences {
  return {
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

export type MotionCoordinatorOptions = {
  preferences(): MotionPreferences
  engine(): Engine
  theme(): Theme
}

export type MotionDebugState = {
  readonly ghosts: number
  readonly pulses: number
  readonly hover: number
}

type Ghost = { readonly pos: Vec2; readonly discR: number; readonly start: number }
type Pulse = { readonly id: string; readonly start: number }
type ActiveBeta = { readonly plan: LambdaMotionPlan; readonly baseColor: string }

const GHOST_MS = 320
const PULSE_MS = 450

const withAlpha = (color: string, alpha: number): string => {
  const byte = Math.max(0, Math.min(255, Math.round(alpha * 255))).toString(16).padStart(2, '0')
  return /^#[0-9a-f]{6}$/i.test(color) ? `${color}${byte}` : color
}

/**
 * Paint-only motion for whole-diagram replacements. Proof actions commit
 * synchronously; this coordinator only remembers outgoing ghosts, incoming
 * pulses, and hover easing.
 */
export class MotionCoordinator {
  readonly #options: MotionCoordinatorOptions
  #ghosts: Ghost[] = []
  #pulses: Pulse[] = []
  #hoverKey: string | null = null
  #hoverSince = 0
  #beta: ActiveBeta | null = null
  #disposed = false

  constructor(options: MotionCoordinatorOptions) {
    this.#options = options
  }

  observeSwap(before: Engine, after: Engine, now: number): void {
    if (!this.#options.preferences().transitionGhosts || this.#disposed) return
    for (const [id, body] of before.bodies) {
      if (!after.bodies.has(id)) {
        this.#ghosts.push({ pos: { ...body.pos }, discR: body.discR * before.scale, start: now })
      }
    }
    for (const id of after.bodies.keys()) {
      if (!before.bodies.has(id)) this.#pulses.push({ id, start: now })
    }
  }

  overlays(now: number): readonly Shape[] {
    if (this.#disposed) return []
    const theme = this.#options.theme()
    const speed = this.#options.preferences().speed
    const shapes: Shape[] = []
    this.#ghosts = this.#ghosts.filter((ghost) => {
      const fraction = (now - ghost.start) / (GHOST_MS / speed)
      if (fraction >= 1) return false
      shapes.push({
        kind: 'circle',
        center: ghost.pos,
        r: ghost.discR * (1 + Math.max(0, fraction) * 0.4),
        fill: withAlpha(theme.ink, (1 - Math.max(0, fraction)) * 0.34),
        stroke: null,
        width: 0,
        insetColor: null,
        glow: null,
      })
      return true
    })
    const engine = this.#options.engine()
    this.#pulses = this.#pulses.filter((pulse) => {
      const fraction = (now - pulse.start) / (PULSE_MS / speed)
      const body = engine.bodies.get(pulse.id)
      if (fraction >= 1 || body === undefined) return false
      shapes.push({
        kind: 'circle',
        center: body.pos,
        r: body.discR * engine.scale + 2 + Math.max(0, fraction) * 6,
        fill: null,
        stroke: withAlpha(theme.interaction.valid, (1 - Math.max(0, fraction)) * 0.54),
        width: 1.8,
        insetColor: null,
        glow: null,
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

  beginBeta(source: Term, step: ReductionStep, baseColor: string): LambdaMotionPlan {
    const plan = planBetaMotion(source, step)
    this.#beta = { plan, baseColor }
    return plan
  }

  #sampleBeta(progress: number): LambdaStrokeFrame | null {
    return this.#beta === null
      ? null
      : sampleBetaMotion(this.#beta.plan, progress, this.#beta.baseColor)
  }

  /** Pointer-driven timeline sampling uses the active structural plan verbatim. */
  scrubBeta(progress: number): LambdaStrokeFrame | null {
    return this.#sampleBeta(progress)
  }

  /** Clock-driven playback uses the same normalized structural plan. */
  playBeta(progress: number): LambdaStrokeFrame | null {
    return this.#sampleBeta(progress)
  }

  /** A discrete step is the settled endpoint of the active structural plan. */
  stepBeta(): LambdaStrokeFrame | null {
    return this.#sampleBeta(1)
  }

  /** Undo, redo, and replay history sample the same plan as direct scrubbing. */
  historyBeta(progress: number): LambdaStrokeFrame | null {
    return this.#sampleBeta(progress)
  }

  debugState(now: number): MotionDebugState {
    return {
      ghosts: this.#ghosts.length,
      pulses: this.#pulses.length,
      hover: this.hoverFraction(now),
    }
  }

  cancel(): void {
    this.#ghosts = []
    this.#pulses = []
    this.#hoverKey = null
    this.#beta = null
  }

  dispose(): void {
    this.cancel()
    this.#disposed = true
  }
}
