import type {
  Diagram,
  DiagramNode,
  NodeId,
  Wire,
  WireId,
} from '../../diagram/diagram'
import { DiagramError, mkDiagram } from '../../diagram/diagram'
import type { ConversionCertificate } from '../../term/certificate'
import { checkConversion } from '../../term/certificate'
import { assertWellFormedTerm, type Term } from '../../term/term'
import { termNodeAt, wireAt } from '../access'
import { RuleError } from '../error'
import {
  mapTermToCommonCarrier,
  validateSlotCorrespondence,
  type SlotCorrespondence,
} from './correspondence'

function replacementAttachments(
  diagram: Diagram,
  correspondence: SlotCorrespondence,
  attachments: Readonly<Record<number, WireId>>,
): ReadonlyMap<number, WireId> {
  const result = new Map<number, WireId>()
  for (const [rawSlot, wire] of Object.entries(attachments)) {
    const slot = Number(rawSlot)
    if (
      !Number.isSafeInteger(slot)
      || slot < 0
      || String(slot) !== rawSlot
      || slot >= correspondence.right.length
    ) {
      throw new DiagramError(
        `attachment slot '${rawSlot}' is outside the replacement interface`,
      )
    }
    const column = correspondence.right[slot]!
    if (correspondence.left.includes(column)) {
      throw new DiagramError(
        `attachment for slot ${slot}, which is not newly added by the replacement interface`,
      )
    }
    if (diagram.wires[wire] === undefined) {
      throw new DiagramError(`unknown wire '${wire}'`)
    }
    result.set(slot, wire)
  }
  for (const [slot, column] of correspondence.right.entries()) {
    if (!correspondence.left.includes(column) && !result.has(slot)) {
      throw new RuleError(
        `new free slot ${slot} requires an attachment wire`,
      )
    }
  }
  return result
}

function replaceTermNode(
  diagram: Diagram,
  nodeId: NodeId,
  node: Extract<DiagramNode, { kind: 'term' }>,
  term: Term,
  correspondence: SlotCorrespondence,
  attachments: Readonly<Record<number, WireId>>,
): Diagram {
  const added = replacementAttachments(diagram, correspondence, attachments)
  const oldWires = correspondence.left.map((_, slot) =>
    wireAt(diagram, nodeId, { kind: 'free', index: slot }))
  const wires: Record<WireId, Wire> = Object.fromEntries(
    Object.entries(diagram.wires).map(([wireId, wire]) => [
      wireId,
      {
        sig: wire.sig,
        endpoints: wire.endpoints.filter((endpoint) =>
          !(endpoint.node === nodeId && endpoint.port.kind === 'free')),
      },
    ]),
  )
  for (const [slot, column] of correspondence.right.entries()) {
    const oldSlot = correspondence.left.indexOf(column)
    const target = oldSlot < 0 ? added.get(slot)! : oldWires[oldSlot]!
    const wire = wires[target]!
    wires[target] = {
      sig: wire.sig,
      endpoints: [
        ...wire.endpoints,
        { node: nodeId, port: { kind: 'free', index: slot } },
      ],
    }
  }
  const nodes: Record<NodeId, DiagramNode> = {
    ...diagram.nodes,
    [nodeId]: {
      kind: 'term',
      region: node.region,
      term,
      freeArity: correspondence.right.length,
    },
  }
  return mkDiagram({
    root: diagram.root,
    regions: { ...diagram.regions },
    nodes,
    wires,
  })
}

/** Replay a stored beta-eta conversion certificate and replace one whole term. */
export function applyLambdaConversion(
  diagram: Diagram,
  node: NodeId,
  term: Term,
  correspondence: SlotCorrespondence,
  certificate: ConversionCertificate,
  attachments: Readonly<Record<number, WireId>> = {},
): Diagram {
  const source = termNodeAt(diagram, node)
  validateSlotCorrespondence(
    correspondence,
    source.freeArity,
    correspondence.right.length,
  )
  try {
    assertWellFormedTerm(term, correspondence.right.length)
  } catch (error) {
    throw new RuleError(
      `replacement term interface rejected: `
      + `${error instanceof Error ? error.message : String(error)}`,
    )
  }
  const check = checkConversion(
    mapTermToCommonCarrier(source.term, correspondence.left),
    mapTermToCommonCarrier(term, correspondence.right),
    certificate,
  )
  if (!check.ok) {
    throw new RuleError(`conversion certificate rejected: ${check.reason}`)
  }
  return replaceTermNode(
    diagram,
    node,
    source,
    term,
    correspondence,
    attachments,
  )
}
