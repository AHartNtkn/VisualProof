import type {
  Diagram,
  Endpoint,
  NodeId,
  RegionId,
  WireId,
} from '../../kernel/diagram/diagram'
import { relSig } from '../../kernel/diagram/sig'
import { bareWireAssembly } from '../../kernel/rules/identity-rules'
import type { ProofContext } from '../../kernel/proof/context'
import { applyStep, type ProofStep } from '../../kernel/proof/step'
import { length, sub } from '../../view/vec'
import { pkey, type Engine } from '../../view/engine'
import type { Shape, Theme } from '../../view/paint'
import type { Vec2 } from '../../view/vec'
import {
  hitTest,
  regionAt,
  wireManipulationHitTest,
} from '../hittest'
import type { PointerClaim, PointerSample } from './viewport'
import { headWireOf } from './wire-ops'

/**
 * One touched site of the drawing gesture. Contacts are a set: the committed
 * step never depends on the order they were made in.
 */
type DrawContact =
  | { readonly kind: 'end'; readonly wire: WireId; readonly endpoint: Endpoint; readonly at: Vec2 }
  | { readonly kind: 'strand'; readonly wire: WireId; readonly at: Vec2 }
  | { readonly kind: 'identity'; readonly node: NodeId; readonly at: Vec2 }
  | { readonly kind: 'blank'; readonly region: RegionId; readonly at: Vec2 }

type PendingDrawing = {
  readonly contacts: Map<string, DrawContact>
  loose: Vec2
}

export type DrawGestureOptions = {
  readonly active: () => boolean
  readonly engine: () => Engine
  readonly diagram: () => Diagram
  readonly viewScale: () => number
  readonly theme: () => Theme
  readonly context: () => ProofContext
  readonly orientation: () => 'forward' | 'backward'
  /** Commit one atomic action; false means the kernel refused it. */
  readonly commit: (
    label: string,
    steps: readonly ProofStep[],
    pointer: Vec2,
  ) => boolean
  /** The contactless drop: the existing spawn prompt picks the signature. */
  readonly openSpawn: (sample: PointerSample, region: RegionId) => void
  /** A still right-click with nothing pending: open the ordinary palette.
      The browser's contextmenu event may fire at press time, before a drag
      can be told from a click, so the gesture owns palette opening. */
  readonly stillMenu: (sample: PointerSample) => void
  readonly refuse: (text: string, pointer: Vec2) => void
}

const HIT_RADIUS_PX = 6

/** Ray-cast point-in-polygon over the stroke's sampled path. */
function strokeEncloses(point: Vec2, polygon: readonly Vec2[]): boolean {
  let inside = false
  for (let i = 0, j = polygon.length - 1; i < polygon.length; j = i++) {
    const a = polygon[i]!
    const b = polygon[j]!
    if (
      (a.y > point.y) !== (b.y > point.y)
      && point.x < ((b.x - a.x) * (point.y - a.y)) / (b.y - a.y) + a.x
    ) inside = !inside
  }
  return inside
}

function contactKey(contact: DrawContact): string {
  switch (contact.kind) {
    case 'end':
      return `e:${contact.wire}:${contact.endpoint.node}:${pkey(contact.endpoint.port)}`
    case 'strand':
      return `s:${contact.wire}`
    case 'identity':
      return `i:${contact.node}`
    case 'blank':
      return `b:${contact.at.x}:${contact.at.y}`
  }
}

/**
 * The comprehension-direction drawing gesture. A right-drag from open space
 * founds a pending drawing whose loose end parks where the stroke released
 * without touching anything (or at the stroke's start when it did). Further
 * right-clicks or right-drags add contacts — wire ends, wire strands,
 * identity nodes, or blank spots. Grabbing the loose end and releasing it
 * commits: the contact type selects the primitive and the drop region is its
 * scope. Contact sets are typed sets; order never matters.
 */
export class DrawGestureController {
  readonly #options: DrawGestureOptions
  #pending: PendingDrawing | null = null
  #stroke: { readonly from: Vec2; at: Vec2 } | null = null
  #suppressMenu = false
  #claimEpoch = 0

  constructor(options: DrawGestureOptions) {
    this.#options = options
  }

  get hasPendingInteraction(): boolean {
    return this.#pending !== null
  }

  /** True exactly once after a gesture consumed the right-button release. */
  consumeMenuSuppression(): boolean {
    const suppressed = this.#suppressMenu
    this.#suppressMenu = false
    return suppressed
  }

  claim(sample: PointerSample): PointerClaim | null {
    if (
      !this.#options.active()
      || sample.button !== 2
      || sample.shiftKey
      || sample.ctrlKey
    ) return null
    const pending = this.#pending
    if (pending !== null && this.#onLooseEnd(pending, sample.world)) {
      return this.#claimDrop(pending)
    }
    return this.#claimStroke(pending, sample.world)
  }

  overlay(): readonly Shape[] {
    const color = this.#options.theme().interaction.valid
    const out: Shape[] = []
    const pending = this.#pending
    if (pending !== null) {
      for (const contact of pending.contacts.values()) {
        out.push({
          kind: 'segment',
          from: contact.at,
          to: pending.loose,
          stroke: color,
          width: 1.6,
          glow: null,
        })
        out.push({
          kind: 'circle',
          center: contact.at,
          r: 3,
          fill: color,
          stroke: color,
          width: 1,
          insetColor: null,
          glow: null,
        })
      }
      out.push({
        kind: 'circle',
        center: pending.loose,
        r: 4.5,
        fill: null,
        stroke: color,
        width: 2,
        insetColor: null,
        glow: null,
      })
    }
    const stroke = this.#stroke
    if (stroke !== null) {
      out.push({
        kind: 'segment',
        from: stroke.from,
        to: stroke.at,
        stroke: color,
        width: 1.6,
        glow: null,
      })
    }
    return out
  }

  cancel(): void {
    this.#claimEpoch++
    this.#pending = null
    this.#stroke = null
  }

  #onLooseEnd(pending: PendingDrawing, point: Vec2): boolean {
    const radius = HIT_RADIUS_PX / this.#options.viewScale()
    return length(sub(point, pending.loose)) <= radius
  }

  /** Grabbing the loose end: releasing it anywhere commits the drawing. */
  #claimDrop(pending: PendingDrawing): PointerClaim {
    this.#suppressMenu = true
    return this.#issueClaim({
      still: 'claim',
      blocksPassiveRelaxation: true,
      move: (sample) => {
        pending.loose = sample.world
      },
      release: (sample) => {
        pending.loose = sample.world
        this.#commit(pending, sample)
      },
      cancel: () => {},
    })
  }

  /** A founding or contact stroke; the release point is what it touches. */
  #claimStroke(
    pending: PendingDrawing | null,
    start: Vec2,
  ): PointerClaim | null {
    const stroke = { from: start, at: start }
    const path: Vec2[] = [start]
    this.#stroke = stroke
    this.#suppressMenu = true
    return this.#issueClaim({
      still: 'claim',
      blocksPassiveRelaxation: true,
      move: (sample) => {
        stroke.at = sample.world
        path.push(sample.world)
      },
      release: (sample, moved) => {
        this.#stroke = null
        const contact = this.#probe(sample.world)
        if (pending === null) {
          // A plain right-click founds nothing; it opens the palette.
          if (!moved) {
            this.#options.stillMenu(sample)
            return
          }
          if (this.#lassoCommit(start, sample, path)) return
          this.#pending = {
            contacts: contact === null
              ? new Map()
              : new Map([[contactKey(contact), contact]]),
            loose: contact === null ? sample.world : start,
          }
          return
        }
        const site = contact ?? {
          kind: 'blank' as const,
          region: regionAt(
            this.#options.engine(),
            this.#options.diagram(),
            sample.world,
          ),
          at: sample.world,
        }
        pending.contacts.set(contactKey(site), site)
      },
      cancel: () => {
        this.#stroke = null
      },
    })
  }

  /**
   * A founding stroke that returns to its start is a drawn cut: enclosing
   * end nodes of exactly one wire commits cutWrap on it. True when this
   * stroke was consumed as a lasso (committed or refused).
   */
  #lassoCommit(
    start: Vec2,
    sample: PointerSample,
    path: readonly Vec2[],
  ): boolean {
    const radius = HIT_RADIUS_PX / this.#options.viewScale()
    if (length(sub(sample.world, start)) > 2 * radius) return false
    const engine = this.#options.engine()
    const diagram = this.#options.diagram()
    const wires = new Set<WireId>()
    for (const body of engine.bodies.values()) {
      if (body.kind !== 'atom' && body.kind !== 'ref') continue
      if (!strokeEncloses(body.pos, path)) continue
      const wire = headWireOf(diagram, body.id)
      if (wire !== null) wires.add(wire)
    }
    if (wires.size === 0) return false
    if (wires.size > 1) {
      this.#options.refuse(
        "the lasso must enclose one wire's end",
        sample.client,
      )
      return true
    }
    const [wire] = wires
    this.#options.commit('cutWrap', [{ rule: 'cutWrap', wire: wire! }], sample.client)
    return true
  }

  /** What one probe point touches, in contact vocabulary. */
  #probe(point: Vec2): DrawContact | null {
    const engine = this.#options.engine()
    const diagram = this.#options.diagram()
    const viewport = { scale: this.#options.viewScale() }
    // Identity discs outrank wire terminals: every terminal on an identity
    // node's rim sits within the disc's halo, so the disc must win there and
    // the terminal stays reachable just outside the rim.
    const hit = hitTest(engine, point, viewport)
    if (hit?.kind === 'node' && diagram.nodes[hit.id]?.kind === 'identity') {
      return { kind: 'identity', node: hit.id, at: point }
    }
    const manipulation = wireManipulationHitTest(engine, point, viewport)
    if (manipulation === null) return null
    if (manipulation.kind === 'endpoint') {
      return {
        kind: 'end',
        wire: manipulation.wire,
        endpoint: manipulation.endpoint,
        at: point,
      }
    }
    return { kind: 'strand', wire: manipulation.wire, at: point }
  }

  #commit(pending: PendingDrawing, sample: PointerSample): void {
    const engine = this.#options.engine()
    const diagram = this.#options.diagram()
    const scope = regionAt(engine, diagram, sample.world)
    const contacts = [...pending.contacts.values()]
    if (contacts.length === 0) {
      this.#pending = null
      this.#options.openSpawn(sample, scope)
      return
    }
    const kinds = [...new Set(contacts.map((contact) => contact.kind))]
    if (kinds.length > 1) {
      this.#options.refuse(
        `one drawing cannot mix ${kinds.join(' and ')} contacts`,
        sample.client,
      )
      return
    }
    const steps = this.#dispatch(diagram, contacts, kinds[0]!, scope, sample)
    if (steps === null) return
    if (this.#options.commit(steps.label, steps.steps, sample.client)) {
      this.#pending = null
    }
  }

  #dispatch(
    diagram: Diagram,
    contacts: readonly DrawContact[],
    kind: DrawContact['kind'],
    scope: RegionId,
    sample: PointerSample,
  ): { readonly label: string; readonly steps: readonly ProofStep[] } | null {
    switch (kind) {
      case 'blank': {
        const sites = contacts
          .filter((contact) => contact.kind === 'blank')
          .map((contact) => ({ region: contact.region, args: [] }))
        // The stroke's own region holds the quantifier: the segment's pins
        // stay there while the ends spawn at the touched sites below it.
        const intro: ProofStep = {
          rule: 'vacuity',
          direction: 'insert',
          assembly: bareWireAssembly('w', scope, relSig([]), ['pin0', 'pin1']),
        }
        let fresh: WireId | undefined
        try {
          const trial = applyStep(
            diagram,
            intro,
            this.#options.context(),
            this.#options.orientation(),
          )
          fresh = Object.keys(trial.wires)
            .find((id) => diagram.wires[id] === undefined)
        } catch (error) {
          this.#options.refuse(
            error instanceof Error ? error.message : String(error),
            sample.client,
          )
          return null
        }
        if (fresh === undefined) {
          this.#options.refuse(
            'spawning produced no wire to give ends to',
            sample.client,
          )
          return null
        }
        return {
          label: 'endsSpawn',
          steps: [intro, { rule: 'endsSpawn', wire: fresh, sites }],
        }
      }
      case 'end': {
        const ends = contacts
          .filter((contact) => contact.kind === 'end')
        const wires = [...new Set(ends.map((contact) => contact.wire))]
        if (wires.length === 1) {
          const wire = wires[0]!
          const moved = new Set(ends.map((contact) =>
            `${contact.endpoint.node}:${pkey(contact.endpoint.port)}`))
          const keep = (diagram.wires[wire]?.endpoints ?? [])
            .filter((endpoint) =>
              !moved.has(`${endpoint.node}:${pkey(endpoint.port)}`))
          return {
            label: 'wireSever',
            steps: [{ rule: 'wireSever', input: { wire, keep, scope } }],
          }
        }
        const nodes = [...new Set(ends.map((contact) => contact.endpoint.node))]
        return {
          label: 'abstractFormal',
          steps: [{ rule: 'abstractFormal', ends: nodes.sort(), scope }],
        }
      }
      case 'identity': {
        const nodes = contacts
          .filter((contact) => contact.kind === 'identity')
          .map((contact) => contact.node)
        return {
          label: 'identityAbstract',
          steps: [{ rule: 'identityAbstract', nodes: nodes.sort(), scope }],
        }
      }
      case 'strand': {
        const wires = [...new Set(contacts
          .filter((contact) => contact.kind === 'strand')
          .map((contact) => contact.wire))]
        if (wires.length < 2) {
          this.#options.refuse(
            'identity insertion needs strands of at least two wires',
            sample.client,
          )
          return null
        }
        return {
          label: 'identityInsert',
          steps: [{ rule: 'identityInsert', region: scope, wires: wires.sort() }],
        }
      }
    }
  }

  #issueClaim(claim: PointerClaim): PointerClaim {
    const epoch = ++this.#claimEpoch
    const current = (): boolean => this.#claimEpoch === epoch
    const retire = (): boolean => {
      if (!current()) return false
      this.#claimEpoch++
      return true
    }
    return {
      still: claim.still,
      blocksPassiveRelaxation: claim.blocksPassiveRelaxation,
      move: (sample) => {
        if (current()) claim.move(sample)
      },
      release: (sample, moved) => {
        if (retire()) claim.release(sample, moved)
      },
      cancel: () => {
        if (retire()) claim.cancel()
      },
    }
  }
}
