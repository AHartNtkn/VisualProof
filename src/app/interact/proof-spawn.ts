import type {
  Diagram,
  DiagramNode,
  NodeId,
  RegionId,
  WireId,
} from '../../kernel/diagram/diagram'
import type { ProofContext } from '../../kernel/proof/context'
import { assertProofContext } from '../../kernel/proof/context'
import type { ProofStep } from '../../kernel/proof/step'
import { definitionSig } from '../../kernel/rules/fold'
import type { Vec2 } from '../../view/vec'
import {
  atomHeadOptions,
  SpawnCascade,
  type SpawnInvocation,
} from './spawn'

export type StructuralSpawnRequest = {
  readonly node: Exclude<DiagramNode, { readonly kind: 'identity' | 'term' }>
  readonly region: RegionId
  readonly wires: readonly WireId[]
}

/** Compile exactly one final-kernel node into its proof primitive. */
export function proofNodeSpawnStep(request: StructuralSpawnRequest): ProofStep {
  switch (request.node.kind) {
    case 'atom': {
      const wire = request.wires[0]
      if (wire === undefined) throw new Error('atom spawn requires its relation head wire')
      return { rule: 'atomSpawn', region: request.region, wire }
    }
    case 'ref':
      return {
        rule: 'refSpawn',
        region: request.region,
        defId: request.node.defId,
        sig: request.node.sig,
      }
  }
}

export type ProofSpawnControllerOptions = {
  readonly host: HTMLElement
  readonly diagram: () => Diagram
  readonly context: () => ProofContext
  readonly commit: (step: ProofStep) => Diagram
  readonly place: (node: NodeId, at: Vec2) => void
  readonly refuse: (text: string, pointer: Vec2) => void
  readonly headWireColor: (wire: WireId) => string
  readonly hoverHeadWire?: (wire: WireId | null) => void
  readonly openChanged?: (open: boolean) => void
}

function introducedNode(before: Diagram, after: Diagram): NodeId {
  const introduced = Object.keys(after.nodes)
    .filter((node) => before.nodes[node] === undefined)
    .sort()
  if (introduced.length !== 1) {
    throw new Error(`structural spawn introduced ${introduced.length} nodes instead of one`)
  }
  return introduced[0]!
}

export class ProofSpawnController {
  readonly #options: ProofSpawnControllerOptions
  readonly #cascade: SpawnCascade

  constructor(options: ProofSpawnControllerOptions) {
    assertProofContext(options.context())
    this.#options = options
    this.#cascade = new SpawnCascade({
      host: options.host,
      spawnRef: ({ defId, invocation }) => this.#attempt(invocation, () => {
        const relation = options.context().relations.get(defId)
        if (relation === undefined) throw new Error(`unknown relation '${defId}'`)
        return proofNodeSpawnStep({
          node: {
            kind: 'ref',
            region: invocation.region,
            defId,
            sig: definitionSig(relation),
          },
          region: invocation.region,
          wires: [],
        })
      }),
      spawnAtom: ({ wire, invocation }) => this.#attempt(invocation, () => {
        const target = options.diagram().wires[wire]
        if (target === undefined || target.sig.kind !== 'rel') {
          throw new Error(`wire '${wire}' is not a relation head`)
        }
        return proofNodeSpawnStep({
          node: { kind: 'atom', region: invocation.region, sig: target.sig },
          region: invocation.region,
          wires: [wire],
        })
      }),
      headWireColor: options.headWireColor,
      ...(options.hoverHeadWire === undefined
        ? {}
        : { hoverHeadWire: options.hoverHeadWire }),
      ...(options.openChanged === undefined
        ? {}
        : { openChanged: options.openChanged }),
    })
  }

  open(invocation: SpawnInvocation): void {
    const diagram = this.#options.diagram()
    const context = this.#options.context()
    assertProofContext(context)
    this.#cascade.open(
      invocation,
      context.relations,
      atomHeadOptions(diagram, invocation.region),
    )
  }

  close(): boolean { return this.#cascade.close() }
  dispose(): void { this.#cascade.dispose() }

  #attempt(invocation: SpawnInvocation, makeStep: () => ProofStep): boolean {
    try {
      const before = this.#options.diagram()
      const after = this.#options.commit(makeStep())
      this.#options.place(introducedNode(before, after), invocation.world)
      return true
    } catch (error) {
      this.#options.refuse(
        error instanceof Error ? error.message : String(error),
        invocation.screen,
      )
      return false
    }
  }
}
