import { freePorts } from '../term/term'
import type { Diagram, NodeId, RegionId } from '../diagram/diagram'
import { cutDepth } from '../diagram/regions'
import { RuleError } from './error'
import { termNodeAt, wireAt } from './access'

export function anchorAvailability(d: Diagram, witnessId: NodeId): RegionId {
  const witness = termNodeAt(d, witnessId)
  const free = freePorts(witness.term)
  if (free.length > 0) {
    throw new RuleError(
      `anchored wire rules require a closed witness; '${witnessId}' has free ports [${free.map((name) => `'${name}'`).join(', ')}]`,
    )
  }
  const wire = wireAt(d, witnessId, { kind: 'output' })
  const scope = d.wires[wire]!.scope
  const depth = cutDepth(d, witness.region)
  let available = witness.region
  while (available !== scope) {
    const region = d.regions[available]!
    if (region.kind === 'sheet') break
    if (cutDepth(d, region.parent) !== depth) break
    available = region.parent
  }
  return available
}
