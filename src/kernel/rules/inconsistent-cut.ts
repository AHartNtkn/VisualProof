import type { Diagram, NodeId, RegionId } from '../diagram/diagram'
import { DiagramError } from '../diagram/diagram'
import { removeSubgraph } from '../diagram/subgraph/splice'
import type { NormalSeparationCertificate } from '../term/certificate'
import { checkNormalSeparation } from '../term/certificate'
import { normalize } from '../term/reduce'
import { termEq } from '../term/term'
import { termNodeAt, wireAt } from './access'
import { RuleError } from './error'

export type InconsistentCutDiscovery =
  | {
    readonly status: 'certified'
    readonly first: NodeId
    readonly second: NodeId
    readonly certificate: NormalSeparationCertificate
  }
  | { readonly status: 'undecided' }
  | { readonly status: 'absent' }

function candidates(d: Diagram, region: RegionId): readonly NodeId[] {
  return Object.keys(d.nodes)
    .filter((id) => {
      const node = d.nodes[id]!
      return node.kind === 'term' && node.region === region && node.freePorts.length === 0
    })
    .sort()
}

function isCut(d: Diagram, region: RegionId): boolean {
  return d.regions[region]?.kind === 'cut'
}

export function hasInconsistentCutCandidate(d: Diagram, region: RegionId): boolean {
  if (!isCut(d, region)) return false
  const ids = candidates(d, region)
  for (let left = 0; left < ids.length; left++) {
    for (let right = left + 1; right < ids.length; right++) {
      if (wireAt(d, ids[left]!, { kind: 'output' }) === wireAt(d, ids[right]!, { kind: 'output' })) {
        return true
      }
    }
  }
  return false
}

export function findInconsistentCutEvidence(
  d: Diagram,
  region: RegionId,
  fuel: number,
): InconsistentCutDiscovery {
  if (!isCut(d, region)) return { status: 'absent' }
  const ids = candidates(d, region)
  let exhausted = false
  for (let left = 0; left < ids.length; left++) {
    for (let right = left + 1; right < ids.length; right++) {
      const first = ids[left]!
      const second = ids[right]!
      if (wireAt(d, first, { kind: 'output' }) !== wireAt(d, second, { kind: 'output' })) continue
      const firstNode = termNodeAt(d, first)
      const secondNode = termNodeAt(d, second)
      const firstResult = normalize(firstNode.term, fuel)
      const secondResult = normalize(secondNode.term, fuel)
      if (firstResult.status === 'fuel-exhausted' || secondResult.status === 'fuel-exhausted') {
        exhausted = true
        continue
      }
      if (termEq(firstResult.term, secondResult.term)) continue
      const certificate: NormalSeparationCertificate = {
        firstSteps: firstResult.path,
        secondSteps: secondResult.path,
      }
      if (!checkNormalSeparation(firstNode.term, secondNode.term, certificate).ok) continue
      return { status: 'certified', first, second, certificate }
    }
  }
  return exhausted ? { status: 'undecided' } : { status: 'absent' }
}

export function applyInconsistentCutElim(
  d: Diagram,
  region: RegionId,
  first: NodeId,
  second: NodeId,
  certificate: NormalSeparationCertificate,
): Diagram {
  const cut = d.regions[region]
  if (cut === undefined) throw new DiagramError(`unknown region '${region}'`)
  if (cut.kind !== 'cut') {
    throw new RuleError(`inconsistent-cut elimination requires a cut; '${region}' is a ${cut.kind}`)
  }
  if (first === second) {
    throw new RuleError('inconsistent-cut elimination requires two distinct term nodes')
  }
  const firstNode = termNodeAt(d, first)
  const secondNode = termNodeAt(d, second)
  if (firstNode.region !== region || secondNode.region !== region) {
    throw new RuleError(`both term nodes must be directly contained in cut '${region}'`)
  }
  if (firstNode.freePorts.length !== 0 || secondNode.freePorts.length !== 0) {
    throw new RuleError('inconsistent-cut elimination requires closed terms')
  }
  if (wireAt(d, first, { kind: 'output' }) !== wireAt(d, second, { kind: 'output' })) {
    throw new RuleError('the two term outputs must share one wire')
  }
  const checked = checkNormalSeparation(firstNode.term, secondNode.term, certificate)
  if (!checked.ok) {
    throw new RuleError(`invalid normal-separation certificate: ${checked.reason}`)
  }
  return removeSubgraph(d, { region: cut.parent, regions: [region], nodes: [], wires: [] })
}
