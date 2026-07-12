import type { Diagram, NodeId, RegionId } from '../../kernel/diagram/diagram'
import type { ProofStep } from '../../kernel/proof/step'
import { parseTerm } from '../../kernel/term/parse'
import { freePorts } from '../../kernel/term/term'
import type { SpawnInvocation } from './spawn'

export function closedTermIntroStep(source: string, region: RegionId): ProofStep {
  const term = parseTerm(source)
  const free = freePorts(term)
  if (free.length > 0) {
    throw new Error(
      `closed-term introduction requires a closed term; free ports [${free.map((name) => `'${name}'`).join(', ')}] remain`,
    )
  }
  return { rule: 'closedTermIntro', region, term }
}

export function introducedNodeId(before: Diagram, after: Diagram): NodeId {
  const introduced = Object.keys(after.nodes).filter((id) => before.nodes[id] === undefined)
  if (introduced.length !== 1) {
    throw new Error(`expected one introduced node, found ${introduced.length}`)
  }
  return introduced[0]!
}

export type ClosedTermSpawnCommit = {
  readonly diagram: Diagram
  readonly node: NodeId
  readonly at: SpawnInvocation['world']
}

export function commitClosedTermSpawn(
  source: string,
  invocation: SpawnInvocation,
  before: Diagram,
  commit: (step: ProofStep) => Diagram,
): ClosedTermSpawnCommit {
  const diagram = commit(closedTermIntroStep(source, invocation.region))
  return { diagram, node: introducedNodeId(before, diagram), at: invocation.world }
}
