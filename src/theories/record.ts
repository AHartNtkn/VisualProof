import type { DiagramWithBoundary } from '../kernel/diagram/boundary'
import type {
  Diagram,
  NodeId,
  RegionId,
  WireId,
} from '../kernel/diagram/diagram'
import type { Sig } from '../kernel/diagram/sig'
import { derivedScope } from '../kernel/diagram/regions'
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
import { nextRemovablePinStep } from '../kernel/proof/pin-sweep'
import { ScopePreservationError } from '../kernel/rules/wire-ends'
import { pinnedForReplay } from '../kernel/proof/theorem'
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
  // Completion pins ride along with many rules; the script's referent is
  // the primary node, so pins (arity-1 identities) don't count here.
  const ids = Object.keys(after.nodes)
    .filter((id) => {
      if (before.nodes[id] !== undefined) return false
      const node = after.nodes[id]!
      if (node.kind === 'identity' && node.arity <= 1) return false
      return region === undefined || node.region === region
    })
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
      && (scope === undefined || derivedScope(after, id) === scope))
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

/**
 * The pin step a `ScopePreservationError` asks for: a fresh arity-1
 * identity node at `scope`, attached to `wireId` via `attachments` (stub
 * growth onto the existing wire, not a new one). The node id is a mint
 * label — `applyVacuityInsert` freshens it. Pure: does not apply the step.
 * Shared by `PrimitiveStepRecorder#recordPin` (below) and the search's
 * auto-pin bundling (`src/generate/search/search.ts`), which resolves the
 * same refusal the same way.
 */
export function pinStep(diagram: Diagram, wireId: WireId, scope: RegionId): ProofStep {
  const wire = diagram.wires[wireId]
  if (wire === undefined) throw new Error(`cannot pin unknown wire '${wireId}'`)
  return {
    rule: 'vacuity',
    direction: 'insert',
    instance: { kind: 'pin', wire: wireId, node: `hold_${wireId}`, region: scope },
  }
}

export class PrimitiveStepRecorder {
  #diagram: Diagram
  readonly #context: ProofContext
  readonly #orientation: Orientation
  readonly #actions: ProofAction[] = []
  readonly #wireRename = new ResolvingView()

  constructor(
    side: DiagramWithBoundary,
    context: ProofContext,
    orientation: Orientation = 'forward',
  ) {
    // Record against the same closed stand-in checkTheorem replays: each
    // boundary entry materialized as its frame pin.
    this.#diagram = pinnedForReplay(side)
    this.#context = context
    this.#orientation = orientation
  }

  get diagram(): Diagram {
    return this.#diagram
  }

  get actions(): readonly ProofAction[] {
    return Object.freeze([...this.#actions])
  }

  #recordPin(wireId: WireId, scope: RegionId): void {
    const action = singleStepAction(`pin ${wireId}`, pinStep(this.#diagram, wireId, scope))
    const before = this.#diagram
    this.#diagram = applyAction(
      this.#diagram,
      action,
      this.#context,
      this.#orientation,
      (_, __, receipt) => {
        this.#absorbTransport(before, receipt.allocation.wires, receipt.transport.image)
      },
    )
    this.#actions.push(action)
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
      && resolved.input.a === resolved.input.b
    ) return
    if (
      resolved.rule === 'identityInsert'
      && new Set(resolved.wires).size < 2
    ) return
    this.#recordAction(singleStepAction(label, resolved))
  }

  /**
   * The drawable bare existential (∃x:σ.⊤) at `region`: a point, then a
   * stub grown from it — two recorded vacuity steps, the rule's own
   * decomposition of the old one-step bare-wire insertion. Returns the
   * real id of the new wire.
   */
  recordBareWire(label: string, region: RegionId, sig: Sig, wireLabel = 'bare'): WireId {
    let before = this.#diagram
    this.record(label, {
      rule: 'vacuity',
      direction: 'insert',
      instance: { kind: 'point', node: `${wireLabel}_end0`, region, sig },
    })
    const point = exactOne(
      'point',
      Object.keys(this.#diagram.nodes)
        .filter((id) => before.nodes[id] === undefined)
        .sort(),
      ` for '${label}'`,
    )
    before = this.#diagram
    this.record(label, {
      rule: 'vacuity',
      direction: 'insert',
      instance: { kind: 'stub', base: point, wire: wireLabel, end: `${wireLabel}_end1`, region },
    })
    return onlyNewWire(before, this.#diagram, region)
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
    this.#recordAction(compileRelationSeverAction(
      label,
      this.#diagram,
      { scope: input.scope, occurrences },
      this.#context,
      this.#orientation,
    ))
  }

  #recordAction(action: ProofAction): void {
    // Old scripts assumed scope rode along invisibly; the typed refusal says
    // exactly which wire to pin where, and the pin is recorded explicitly.
    for (let guard = 0; ; guard += 1) {
      if (guard > 64) throw new Error('recorder pinned 64 wires without progress')
      try {
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
        break
      } catch (error) {
        const cause = error instanceof Error && error.cause instanceof ScopePreservationError
          ? error.cause
          : error instanceof ScopePreservationError ? error : null
        if (cause === null) throw error
        this.#recordPin(cause.wireId, cause.scope)
      }
    }
    this.#actions.push(action)
    this.#tidy()
  }

  /**
   * Re-impose, as EXPLICIT recorded steps, the tidying the old eager
   * normalizer did silently (spec §10.4): contract single-wire identity
   * nodes, collapse one-point-eligible ones, fuse co-regional sharing
   * pairs — then sweep ⊤-idle scaffolding pins. Scripts authored against
   * the eager shapes replay unchanged; the history says everything.
   */
  #tidy(): void {
    for (;;) {
      const step = this.#nextIdentityStep() ?? nextRemovablePinStep(this.#diagram)
      if (step === null) return
      const before = this.#diagram
      const action = singleStepAction('tidy', step)
      this.#diagram = applyAction(
        this.#diagram,
        action,
        this.#context,
        this.#orientation,
        (_, __, receipt) => {
          this.#absorbTransport(before, receipt.allocation.wires, receipt.transport.image)
        },
      )
      this.#actions.push(action)
    }
  }

  #nextIdentityStep(): ProofStep | null {
    const d = this.#diagram
    const identityIds = Object.keys(d.nodes)
      .filter((id) => {
        const node = d.nodes[id]!
        return node.kind === 'identity' && node.arity >= 2
      })
      .sort()
    const incidentOf = (nodeId: NodeId): WireId[] =>
      Object.keys(d.wires)
        .filter((wireId) => d.wires[wireId]!.endpoints.some((ep) => ep.node === nodeId))
        .sort()

    // Old rule 1: a node with all ports on one wire contracts toward unary
    // (the pin sweep finishes the job when the leftover holds nothing).
    for (const nodeId of identityIds) {
      const incident = incidentOf(nodeId)
      if (incident.length !== 1) continue
      const wire = d.wires[incident[0]!]!
      const ports = wire.endpoints.filter((ep) => ep.node === nodeId).length
      if (wire.endpoints.length - ports + 1 < 2) continue
      return {
        rule: 'presentation',
        input: {
          region: d.nodes[nodeId]!.region,
          removeNodes: [nodeId],
          addNodes: { [nodeId]: [incident[0]!] },
        },
      }
    }
    // Old rule 2 (one-point): at most one incident wire quantified outside
    // the node's region — collapse the rest onto it.
    for (const nodeId of identityIds) {
      const node = d.nodes[nodeId]!
      const incident = incidentOf(nodeId)
      if (incident.length < 2) continue
      const outer = incident.filter((wireId) =>
        derivedScope(d, wireId) !== node.region)
      if (outer.length > 1) continue
      const survivor = outer[0] ?? incident[0]!
      const absorbed = incident.filter((wireId) => wireId !== survivor)
      return {
        rule: 'identification',
        input: { kind: 'collapse', node: nodeId, survivor, absorbed },
      }
    }
    // Old rule 3: same-region nodes sharing a wire fuse.
    for (const leftId of identityIds) {
      const left = d.nodes[leftId]!
      const leftWires = new Set(incidentOf(leftId))
      for (const rightId of identityIds) {
        if (rightId <= leftId) continue
        const right = d.nodes[rightId]!
        if (left.region !== right.region) continue
        const rightWires = incidentOf(rightId)
        if (!rightWires.some((wireId) => leftWires.has(wireId))) continue
        const union = [...new Set([...leftWires, ...rightWires])].sort()
        return {
          rule: 'presentation',
          input: {
            region: left.region,
            removeNodes: [leftId, rightId],
            addNodes: { [leftId]: union },
          },
        }
      }
    }
    return null
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
