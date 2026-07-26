import type {
  Diagram,
  NodeId,
  RegionId,
  WireId,
} from '../kernel/diagram/diagram'
import {
  applyAction,
  singleStepAction,
  type ProofAction,
} from '../kernel/proof/action'
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
    const action = singleStepAction(label, step)
    const next = applyAction(
      this.#diagram,
      action,
      this.#context,
      this.#orientation,
    )
    this.#diagram = next
    this.#actions.push(action)
  }
}
