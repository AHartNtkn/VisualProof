import type { DiagramWithBoundary } from '../kernel/diagram/boundary'
import type {
  Diagram,
  NodeId,
  RegionId,
  WireId,
} from '../kernel/diagram/diagram'
import type { SubgraphSelection } from '../kernel/diagram/subgraph/selection'
import {
  applyAction,
  singleStepAction,
  type ProofAction,
} from '../kernel/proof/action'
import {
  compileRelationJoinAction,
  compileRelationSeverAction,
} from '../kernel/proof/compile-content'
import { mapStepIds } from '../kernel/proof/compose'
import type { ProofContext } from '../kernel/proof/context'
import type { ProofStep } from '../kernel/proof/step'

type Orientation = 'forward' | 'backward'

function exactOne<T extends string>(
  kind: string,
  ids: readonly T[],
  qualifier: string,
): T {
  if (ids.length !== 1) {
    throw new Error(
      `expected exactly one new ${kind}${qualifier}, found ${ids.length}`
      + (ids.length === 0 ? '' : ` (${ids.join(', ')})`),
    )
  }
  return ids[0]!
}

export function onlyNewNode(
  before: Diagram,
  after: Diagram,
  region?: RegionId,
): NodeId {
  const ids = Object.keys(after.nodes)
    .filter((id) =>
      before.nodes[id] === undefined
      && (region === undefined || after.nodes[id]!.region === region))
    .sort()
  return exactOne('node', ids, region === undefined ? '' : ` in '${region}'`)
}

export function onlyNewWire(
  before: Diagram,
  after: Diagram,
  scope?: RegionId,
): WireId {
  const ids = Object.keys(after.wires)
    .filter((id) =>
      before.wires[id] === undefined
      && (scope === undefined || after.wires[id]!.scope === scope))
    .sort()
  return exactOne('wire', ids, scope === undefined ? '' : ` in '${scope}'`)
}

export function onlyNewCut(
  before: Diagram,
  after: Diagram,
  parent?: RegionId,
): RegionId {
  const ids = Object.keys(after.regions)
    .filter((id) => {
      if (before.regions[id] !== undefined) return false
      const region = after.regions[id]!
      return region.kind === 'cut'
        && (parent === undefined || region.parent === parent)
    })
    .sort()
  return exactOne('cut', ids, parent === undefined ? '' : ` under '${parent}'`)
}

export class PrimitiveStepRecorder {
  #diagram: Diagram
  readonly #context: ProofContext
  readonly #orientation: Orientation
  readonly #actions: ProofAction[] = []
  readonly #wireRename = new ResolvingView()

  constructor(
    diagram: Diagram,
    context: ProofContext,
    orientation: Orientation = 'forward',
  ) {
    this.#diagram = diagram
    this.#context = context
    this.#orientation = orientation
  }

  get diagram(): Diagram {
    return this.#diagram
  }

  get actions(): readonly ProofAction[] {
    return Object.freeze([...this.#actions])
  }

  record(label: string, step: ProofStep): void {
    const resolved = mapStepIds(step, {
      regions: identityView,
      nodes: identityView,
      wires: this.#wireRename,
    })
    // An equality assertion whose wires normalization has already merged is
    // satisfied by the diagram as it stands; the step degenerates to the
    // identity action and is elided. Every other resolved step stays loud.
    if (
      resolved.rule === 'wireJoin'
      && resolved.input.kind === 'iota'
      && resolved.input.a === resolved.input.b
    ) return
    if (
      resolved.rule === 'identityInsert'
      && new Set(resolved.wires).size < 2
    ) return
    this.#recordAction(singleStepAction(label, resolved))
  }

  /**
   * Record one monolithically specified relation grounding as its compiled
   * primitive sequence, under one labeled action.
   */
  recordRelationJoin(
    label: string,
    input: {
      readonly wire: WireId
      readonly content: DiagramWithBoundary
      readonly parameters: readonly WireId[]
    },
  ): void {
    const wire = this.#wireRename.get(input.wire)
    const parameters = input.parameters.map((parameter) =>
      this.#wireRename.get(parameter))
    this.#recordAction(compileRelationJoinAction(
      label,
      this.#diagram,
      wire,
      input.content,
      parameters,
      this.#context,
      this.#orientation,
    ))
  }

  /**
   * Record one monolithically specified relation abstraction as its compiled
   * primitive sequence, under one labeled action.
   */
  recordRelationSever(
    label: string,
    input: {
      readonly scope: RegionId
      readonly occurrences: readonly {
        readonly sel: SubgraphSelection
        readonly args: readonly WireId[]
      }[]
    },
  ): void {
    const occurrences = input.occurrences.map((occurrence) => ({
      sel: occurrence.sel,
      args: occurrence.args.map((wire) => this.#wireRename.get(wire)),
    }))
    if (process.env.PROBE_SEVER !== undefined) {
      for (const occurrence of occurrences) {
        console.log('[sever occurrence]', JSON.stringify(occurrence.sel))
      }
      const region = occurrences[0]!.sel.region
      console.log('[region nodes]', JSON.stringify(
        Object.entries(this.#diagram.nodes)
          .filter(([, node]) => node.region === region)
          .map(([id, node]) => ({ id, kind: node.kind }))))
    }
    this.#recordAction(compileRelationSeverAction(
      label,
      this.#diagram,
      { kind: 'relation', scope: input.scope, occurrences },
      this.#context,
      this.#orientation,
    ))
  }

  #recordAction(action: ProofAction): void {
    const before = this.#diagram
    const next = applyAction(
      this.#diagram,
      action,
      this.#context,
      this.#orientation,
      (_, __, receipt) => {
        this.#absorbTransport(before, receipt.allocation.wires, receipt.transport.image)
      },
    )
    this.#diagram = next
    this.#actions.push(action)
  }

  /**
   * Fold one step's normalization transport into the persistent rename view,
   * so scripts keep addressing wires by the ids they captured even after a
   * later normalization merges them. Wires with no surviving image drop out
   * and stay loud errors when referenced.
   */
  #absorbTransport(
    before: Diagram,
    minted: readonly string[],
    image: (wire: WireId) => WireId | undefined,
  ): void {
    // A minted id may recycle the name of a previously absorbed wire; the
    // name is reborn and now denotes the new wire, so any stale rename keyed
    // by it is invalid.
    for (const id of minted) this.#wireRename.delete(id)
    const stepRename = new Map<WireId, WireId | undefined>()
    for (const wireId of [...Object.keys(before.wires), ...minted]) {
      const mapped = image(wireId)
      if (mapped !== wireId) stepRename.set(wireId, mapped)
    }
    if (stepRename.size === 0) return
    for (const [origin, current] of this.#wireRename) {
      if (stepRename.has(current)) {
        const next = stepRename.get(current)
        if (next === undefined) this.#wireRename.delete(origin)
        else this.#wireRename.set(origin, next)
      }
    }
    for (const [origin, current] of stepRename) {
      if (!this.#wireRename.has(origin)) {
        if (current === undefined) this.#wireRename.delete(origin)
        else this.#wireRename.set(origin, current)
      }
    }
  }
}

/**
 * A total ReadonlyMap view: ids without a recorded rename resolve to
 * themselves. This is what makes `mapStepIds` usable with the partial rename
 * relation normalization produces.
 */
class ResolvingView extends Map<string, string> {
  override get(key: string): string {
    return super.get(key) ?? key
  }
}

const identityView: ReadonlyMap<string, string> = new ResolvingView()
