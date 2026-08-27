import type { Diagram, NodeId, WireId } from '../kernel/diagram/diagram'
import type { ProofStep } from '../kernel/proof/step'
import { termNodeAt, wireAt } from '../kernel/rules/access'
import {
  applyLambdaConversion,
  proposeSlotCorrespondence,
  type SlotCorrespondence,
} from '../kernel/rules/lambda'
import type { ConversionCertificate } from '../kernel/term/certificate'
import {
  compactFreeInterface,
  freeIdentifierSlot,
} from '../kernel/term/interface'
import type { ParsedTerm } from '../kernel/term/parse'
import type { Term } from '../kernel/term/term'

export type LambdaConversionTarget =
  | { readonly kind: 'existingSlots'; readonly term: Term }
  | { readonly kind: 'parsed'; readonly parsed: ParsedTerm }

export type AuthoredLambdaConversionTarget = {
  readonly term: Term
  readonly correspondence: SlotCorrespondence
}

function sourceWires(diagram: Diagram, node: NodeId): WireId[] {
  const source = termNodeAt(diagram, node)
  return Array.from({ length: source.freeArity }, (_, slot) =>
    wireAt(diagram, node, { kind: 'free', index: slot }))
}

/** The only app-layer authority for constructing a Lambda conversion target. */
export function authorLambdaConversionTarget(
  diagram: Diagram,
  node: NodeId,
  target: LambdaConversionTarget,
): AuthoredLambdaConversionTarget {
  const source = termNodeAt(diagram, node)
  const wires = sourceWires(diagram, node)
  if (target.kind === 'existingSlots') {
    const compact = compactFreeInterface(target.term, wires)
    return {
      term: compact.term,
      correspondence: proposeSlotCorrespondence(wires, compact.carriers),
    }
  }

  const targetNames = target.parsed.freeIdentifiers
  const assigned: Array<number | null> = targetNames.map((identifier) => {
    const slot = freeIdentifierSlot(identifier)
    if (slot === null) return null
    if (slot >= source.freeArity) {
      throw new Error(
        `conversion target free identifier '${identifier}' is outside `
        + `the source interface 0..<${source.freeArity}`,
      )
    }
    return slot
  })
  const usedSourceSlots = new Set(assigned.filter(
    (slot): slot is number => slot !== null,
  ))
  const remainingSourceSlots = Array.from({ length: source.freeArity }, (_, slot) => slot)
    .filter((slot) => !usedSourceSlots.has(slot))
  let remaining = 0
  const rightCarriers: Array<WireId | object> = assigned.map((sourceSlot) => {
    if (sourceSlot !== null) return wires[sourceSlot]!
    const paired = remainingSourceSlots[remaining++]
    if (paired !== undefined) return wires[paired]!
    return {}
  })
  return {
    term: target.parsed.term,
    correspondence: proposeSlotCorrespondence<WireId | object>(wires, rightCarriers),
  }
}

export function completeLambdaConversion(
  diagram: Diagram,
  node: NodeId,
  target: AuthoredLambdaConversionTarget,
  certificate: ConversionCertificate,
  attachments: Readonly<Record<number, WireId>> = {},
): { readonly diagram: Diagram; readonly step: ProofStep } {
  const step: ProofStep = {
    rule: 'lambdaConversion',
    node,
    term: target.term,
    correspondence: target.correspondence,
    certificate,
    attachments,
  }
  return {
    diagram: applyLambdaConversion(
      diagram,
      node,
      target.term,
      target.correspondence,
      certificate,
      attachments,
    ),
    step,
  }
}
