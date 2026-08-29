import type { ConversionCertificate } from '../../term/certificate'
import { checkConversion } from '../../term/certificate'
import type { Diagram, NodeId, Wire, WireId } from '../../diagram/diagram'
import { mkDiagram } from '../../diagram/diagram'
import { cutDepth, derivedScope, isAncestorOrEqual } from '../../diagram/regions'
import { termNodeAt, wireAt } from '../access'
import { mapFreeSlots } from '../../term/interface'
import { RuleError } from '../error'
import {
  validateSlotCorrespondence,
  validateSlotCorrespondenceWires,
  type SlotCorrespondence,
} from './correspondence'

/** Join the outputs of two locally convertible whole terms. */
export function applyLambdaCongruenceJoin(
  diagram: Diagram,
  a: NodeId,
  b: NodeId,
  certificate: ConversionCertificate,
  correspondence: SlotCorrespondence,
): Diagram {
  if (a === b) {
    throw new RuleError(`congruence join needs two distinct nodes; got '${a}' twice`)
  }
  const left = termNodeAt(diagram, a)
  const right = termNodeAt(diagram, b)
  if (left.region !== right.region) {
    throw new RuleError(
      `congruence join requires both nodes in one region; `
      + `'${a}' is in '${left.region}', '${b}' in '${right.region}'`,
    )
  }
  validateSlotCorrespondence(
    correspondence,
    left.freeArity,
    right.freeArity,
  )
  const checked = checkConversion(
    mapFreeSlots(left.term, correspondence.left),
    mapFreeSlots(right.term, correspondence.right),
    certificate,
  )
  if (!checked.ok) {
    throw new RuleError(`congruence certificate rejected: ${checked.reason}`)
  }

  validateSlotCorrespondenceWires(diagram, a, b, correspondence)

  const outputA = wireAt(diagram, a, { kind: 'output' })
  const outputB = wireAt(diagram, b, { kind: 'output' })
  if (outputA === outputB) {
    throw new RuleError(`outputs of '${a}' and '${b}' already share wire '${outputA}'`)
  }
  const nodeDepth = cutDepth(diagram, left.region)
  for (const [node, output] of [[a, outputA], [b, outputB]] as const) {
    const scope = derivedScope(diagram, output)
    if (cutDepth(diagram, scope) !== nodeDepth) {
      throw new RuleError(
        `congruence join requires no cut between an output's scope and the nodes' region; `
        + `wire '${output}' of '${node}' is scoped at '${scope}'`,
      )
    }
  }
  const scopeA = derivedScope(diagram, outputA)
  const scopeB = derivedScope(diagram, outputB)
  const keep = isAncestorOrEqual(diagram, scopeA, scopeB) ? outputA : outputB
  const drop = keep === outputA ? outputB : outputA
  const wires: Record<WireId, Wire> = {}
  for (const [wireId, wire] of Object.entries(diagram.wires)) {
    if (wireId === drop) continue
    wires[wireId] = wireId === keep
      ? {
          sig: wire.sig,
          endpoints: [...wire.endpoints, ...diagram.wires[drop]!.endpoints],
        }
      : wire
  }
  return mkDiagram({
    root: diagram.root,
    regions: { ...diagram.regions },
    nodes: { ...diagram.nodes },
    wires,
  })
}
