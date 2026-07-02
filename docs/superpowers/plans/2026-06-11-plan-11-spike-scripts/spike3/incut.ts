// inCutNat: the ORIGINAL canonical natRelation (frege.ts) with exactly one change:
// w0's scope moves from root to rB. Guard = one self-contained cut; no surface zeros.
// Reading: not exists R exists w0 [Z(w0) ^ R(w0) ^ Cl(R) ^ not R(x)].
import { DiagramBuilder } from '/home/ahart/Documents/VisualProofAssistant/src/kernel/diagram/builder'
import { mkDiagramWithBoundary, type DiagramWithBoundary } from '/home/ahart/Documents/VisualProofAssistant/src/kernel/diagram/boundary'
import type { Endpoint, NodeId, RegionId, WireId } from '/home/ahart/Documents/VisualProofAssistant/src/kernel/diagram/diagram'
import { p } from '/tmp/spike2/lib'

/** Self-contained inCutNat guard at `parent`; only the x-line leaves the cut. */
export function buildInCutNat(
  b: DiagramBuilder,
  parent: RegionId,
  extraWx: readonly Endpoint[] = [],
): { cutN: RegionId; w0: WireId; wx: WireId; nz: NodeId } {
  const cutN = b.cut(parent)
  const rB = b.bubble(cutN, 1)
  const nz = b.termNode(rB, p('ZERO'))
  const a0 = b.atom(rB, rB)
  const w0 = b.wire(rB, [
    { node: nz, port: { kind: 'output' } },
    { node: a0, port: { kind: 'arg', index: 0 } },
  ])
  const cut2 = b.cut(rB)
  const a1 = b.atom(cut2, rB)
  const ny = b.termNode(cut2, p('SUCC q'))
  b.wire(cut2, [
    { node: a1, port: { kind: 'arg', index: 0 } },
    { node: ny, port: { kind: 'freeVar', name: 'q' } },
  ])
  const cut3 = b.cut(cut2)
  const a2 = b.atom(cut3, rB)
  b.wire(cut2, [
    { node: ny, port: { kind: 'output' } },
    { node: a2, port: { kind: 'arg', index: 0 } },
  ])
  const cut4 = b.cut(rB)
  const a3 = b.atom(cut4, rB)
  const wx = b.wire(parent, [{ node: a3, port: { kind: 'arg', index: 0 } }, ...extraWx])
  return { cutN, w0, wx, nz }
}

export const P1term = p('PLUS q q_0')
export const P2term = p('PLUS q_0 q')

/** plusComm comp R(x) with the embedded N(b^) as a self-contained inCutNat guard. */
export function buildComp3(): DiagramWithBoundary {
  const b = new DiagramBuilder()
  const cutH = b.cut(b.root)
  const cutC = b.cut(cutH)
  const P1 = b.termNode(cutC, P1term)
  const P2 = b.termNode(cutC, P2term)
  const wq = b.wire(b.root, [
    { node: P1, port: { kind: 'freeVar', name: 'q' } },
    { node: P2, port: { kind: 'freeVar', name: 'q' } },
  ])
  b.wire(cutC, [{ node: P1, port: { kind: 'output' } }, { node: P2, port: { kind: 'output' } }])
  buildInCutNat(b, cutH, [
    { node: P1, port: { kind: 'freeVar', name: 'q_0' } },
    { node: P2, port: { kind: 'freeVar', name: 'q_0' } },
  ])
  return mkDiagramWithBoundary(b.build(), [wq])
}
