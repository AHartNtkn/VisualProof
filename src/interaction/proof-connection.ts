import type { Diagram, Endpoint, NodeId, RegionId, WireId } from '../kernel/diagram/diagram'
import { convertible } from '../kernel/term/convert'
import type { ConversionCertificate } from '../kernel/term/certificate'
import type { ProofStep } from '../kernel/proof/step'
import { applyStep } from '../kernel/proof/step'
import { EMPTY_PROOF_CONTEXT } from '../kernel/proof/context'
import { termNodeAt, wireAt } from '../kernel/rules/access'
import {
  mapTermToCommonCarrier,
  type PortCorrespondence,
} from '../kernel/rules/port-correspondence'
import type { ConnectionEnd } from './controllers/connection'

export type ProofOrientation = 'forward' | 'backward'

/** Match declared ports already sharing a host wire and make all remaining
    ports one-sided. The kernel rechecks the resulting correspondence. */
export function proposeAttachedPortCorrespondence(
  diagram: Diagram,
  leftId: NodeId,
  rightId: NodeId,
): PortCorrespondence {
  const leftNode = termNodeAt(diagram, leftId)
  const rightNode = termNodeAt(diagram, rightId)
  const left = new Map<string, number>()
  const right = new Map<string, number>()
  const usedRight = new Set<string>()
  let commonArity = 0
  for (const leftName of leftNode.freePorts) {
    const leftWire = wireAt(diagram, leftId, { kind: 'freeVar', name: leftName })
    const rightName = rightNode.freePorts.find((candidate) =>
      !usedRight.has(candidate)
      && wireAt(diagram, rightId, { kind: 'freeVar', name: candidate }) === leftWire)
    if (rightName === undefined) continue
    left.set(leftName, commonArity)
    right.set(rightName, commonArity)
    usedRight.add(rightName)
    commonArity += 1
  }
  for (const name of leftNode.freePorts) if (!left.has(name)) left.set(name, commonArity++)
  for (const name of rightNode.freePorts) if (!right.has(name)) right.set(name, commonArity++)
  return { commonArity, left: Object.fromEntries(left), right: Object.fromEntries(right) }
}

function outputNodes(diagram: Diagram, wire: WireId): NodeId[] {
  return diagram.wires[wire]!.endpoints
    .filter((endpoint) => endpoint.port.kind === 'output' && diagram.nodes[endpoint.node]?.kind === 'term')
    .map((endpoint) => endpoint.node)
}

function anchoredSplitCandidate(
  diagram: Diagram,
  wire: WireId,
  source: Endpoint | null,
  target: Endpoint | null,
): ProofStep | null {
  if (source === null || target === null || source.node === target.node) return null
  const [witness, moved] = source.port.kind === 'output'
    ? [source, target]
    : target.port.kind === 'output'
      ? [target, source]
      : [null, null]
  if (witness === null || moved === null || diagram.nodes[witness.node]?.kind !== 'term') return null
  const targetRegion: RegionId = diagram.nodes[moved.node]!.region
  return { rule: 'anchoredWireSplit', wire, witness: witness.node, endpoints: [moved], target: targetRegion }
}

/** Resolve one graphical connection gesture to one replayable proof step.
    Every candidate is preflighted through the real kernel in deterministic
    order; the first accepted justification owns the gesture. */
export function proofConnectionStep(
  diagram: Diagram,
  source: ConnectionEnd,
  target: ConnectionEnd,
  orientation: ProofOrientation,
  fuel: number,
): ProofStep {
  if (source.wire === target.wire) {
    const a = source.endpoint
    const b = target.endpoint
    if (a !== null && b !== null && a.port.kind === 'output' && b.port.kind === 'output') {
      if (a.node === b.node || diagram.nodes[a.node]?.kind !== 'term' || diagram.nodes[b.node]?.kind !== 'term') {
        throw new Error("release on another term's output strand to compare arguments")
      }
      const step: ProofStep = {
        rule: 'headStrip', a: a.node, b: b.node,
        correspondence: proposeAttachedPortCorrespondence(diagram, a.node, b.node),
      }
      applyStep(diagram, step, EMPTY_PROOF_CONTEXT, orientation)
      return step
    }
    const split = anchoredSplitCandidate(diagram, source.wire, a, b)
    if (split !== null) {
      applyStep(diagram, split, EMPTY_PROOF_CONTEXT, orientation)
      return split
    }
    throw new Error("release on another term's output strand or a compatible endpoint strand of the same line")
  }

  const candidates: ProofStep[] = [{ rule: 'wireJoin', a: source.wire, b: target.wire }]
  const left = outputNodes(diagram, source.wire)
  const right = outputNodes(diagram, target.wire)
  const concreteOutput = (end: ConnectionEnd): NodeId | null => end.endpoint?.port.kind === 'output'
    && diagram.nodes[end.endpoint.node]?.kind === 'term' ? end.endpoint.node : null
  const sourceNode = concreteOutput(source)
  const targetNode = concreteOutput(target)
  const leftCandidates = sourceNode === null ? left : [sourceNode]
  const rightCandidates = targetNode === null ? right : [targetNode]
  const unambiguous = leftCandidates.length === 1 && rightCandidates.length === 1
  const convertiblePairs: Array<{ a: NodeId; b: NodeId; certificate: ConversionCertificate }> = []
  if (unambiguous) for (const a of leftCandidates) for (const b of rightCandidates) {
    const leftNode = termNodeAt(diagram, a)
    const rightNode = termNodeAt(diagram, b)
    const correspondence = proposeAttachedPortCorrespondence(diagram, a, b)
    const result = convertible(
      mapTermToCommonCarrier(leftNode.term, correspondence.left),
      mapTermToCommonCarrier(rightNode.term, correspondence.right),
      fuel,
    )
    if (result.status !== 'convertible') continue
    convertiblePairs.push({ a, b, certificate: result.certificate })
    candidates.push({ rule: 'congruenceJoin', a, b, certificate: result.certificate, correspondence })
  }
  for (const pair of convertiblePairs) {
    candidates.push({ rule: 'anchoredWireContract', redundant: pair.a, survivor: pair.b, certificate: pair.certificate })
    candidates.push({
      rule: 'anchoredWireContract', redundant: pair.b, survivor: pair.a,
      certificate: { leftSteps: pair.certificate.rightSteps, rightSteps: pair.certificate.leftSteps },
    })
  }
  for (const candidate of candidates) {
    try {
      applyStep(diagram, candidate, EMPTY_PROOF_CONTEXT, orientation)
      return candidate
    } catch {}
  }
  if (!unambiguous && (leftCandidates.length > 1 || rightCandidates.length > 1)) {
    throw new Error('proof connection is ambiguous; drag from one producer output strand to the other')
  }
  throw new Error(`no valid proof connection joins lines '${source.wire}' and '${target.wire}'`)
}
