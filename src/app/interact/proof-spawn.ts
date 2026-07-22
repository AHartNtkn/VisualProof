import type { Diagram, NodeId, RegionId, WireId } from '../../kernel/diagram/diagram'
import type { ProofContext } from '../../kernel/proof/context'
import { assertProofContext } from '../../kernel/proof/context'
import type { ProofStep } from '../../kernel/proof/step'
import { relationSig } from '../../theories/macros'
import { parseTerm } from '../../kernel/term/parse'
import { freePorts } from '../../kernel/term/term'
import type { Vec2 } from '../../view/vec'
import { introducedNodeId } from './closed-term-intro'
import { boundPredicateOptions, SpawnCascade, type SpawnInvocation } from './spawn'

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

export function proofTermSpawnStep(source: string, region: RegionId): ProofStep {
  const term = parseTerm(source)
  const declaredFreePorts = freePorts(term)
  return declaredFreePorts.length === 0
    ? { rule: 'closedTermIntro', region, term }
    : { rule: 'openTermSpawn', region, term, freePorts: declaredFreePorts }
}

/** Shared Proof-mode policy for the ordinary construction cascade. */
export class ProofSpawnController {
  readonly #options: ProofSpawnControllerOptions
  readonly #cascade: SpawnCascade

  constructor(options: ProofSpawnControllerOptions) {
    assertProofContext(options.context())
    this.#options = options
    this.#cascade = new SpawnCascade({
      host: options.host,
      spawnTerm: ({ source, invocation }) => this.#attempt(invocation, () => proofTermSpawnStep(source, invocation.region)),
      spawnRelation: ({ defId, invocation }) => this.#attempt(invocation, () => {
        const relation = options.context().relations.get(defId)
        if (relation === undefined) throw new Error(`unknown relation '${defId}'`)
        return { rule: 'relationSpawn', region: invocation.region, defId, sig: relationSig(relation) }
      }),
      spawnBoundPredicate: ({ wire, invocation }) => this.#attempt(invocation, () => ({
        rule: 'boundRelationSpawn', region: invocation.region, wire,
      })),
      headWireColor: options.headWireColor,
      ...(options.hoverHeadWire === undefined ? {} : { hoverHeadWire: options.hoverHeadWire }),
      ...(options.openChanged === undefined ? {} : { openChanged: options.openChanged }),
    })
  }

  open(invocation: SpawnInvocation): void {
    const d = this.#options.diagram()
    const context = this.#options.context()
    assertProofContext(context)
    this.#cascade.open(invocation, context.relations, boundPredicateOptions(d, invocation.region))
  }

  close(): boolean { return this.#cascade.close() }
  dispose(): void { this.#cascade.dispose() }

  #attempt(invocation: SpawnInvocation, step: () => ProofStep): boolean {
    try {
      const before = this.#options.diagram()
      const after = this.#options.commit(step())
      this.#options.place(introducedNodeId(before, after), invocation.world)
      return true
    } catch (error) {
      this.#options.refuse(error instanceof Error ? error.message : String(error), invocation.screen)
      return false
    }
  }
}
