// plusComm comp R(x) := forall b [N(b) -> PLUS x b ~ PLUS b x], closed 1-ary:
// cut_H[ rooted-N(b) with internal witness ; cut_C[ PLUS q q_0 -o- PLUS q_0 q ] ]
// stub port 'q' (x), internal-b port 'q_0' (names pinned by succShiftS pair).
import { DiagramBuilder } from '../../../../src/kernel/diagram/builder'
import { mkDiagramWithBoundary, type DiagramWithBoundary } from '../../../../src/kernel/diagram/boundary'
import type { Endpoint, NodeId, RegionId, WireId } from '../../../../src/kernel/diagram/diagram'
import { p } from './lib'

/** The N-cut shape alone: a0 (base atom) and a3 (conclusion atom) left for the caller to wire. */
export function buildNatCut(b: DiagramBuilder, parent: RegionId): { cutN: RegionId; a0: NodeId; a3: NodeId } {
  const cutN = b.cut(parent)
  const rB = b.bubble(cutN, 1)
  const a0 = b.atom(rB, rB)
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
  return { cutN, a0, a3 }
}

/** rooted-N(x) with all top-level parts at `region`; extraWx = extra endpoints for the x-line. */
export function buildNatAt(
  b: DiagramBuilder,
  region: RegionId,
  extraWx: readonly Endpoint[] = [],
): { nz: NodeId; w0: WireId; wx: WireId; cutN: RegionId } {
  const nz = b.termNode(region, p('ZERO'))
  const { cutN, a0, a3 } = buildNatCut(b, region)
  const w0 = b.wire(region, [
    { node: nz, port: { kind: 'output' } },
    { node: a0, port: { kind: 'arg', index: 0 } },
  ])
  const wx = b.wire(region, [{ node: a3, port: { kind: 'arg', index: 0 } }, ...extraWx])
  return { nz, w0, wx, cutN }
}

export const P1term = p('PLUS q q_0')
export const P2term = p('PLUS q_0 q')

export function buildComp(): DiagramWithBoundary {
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
  buildNatAt(b, cutH, [
    { node: P1, port: { kind: 'freeVar', name: 'q_0' } },
    { node: P2, port: { kind: 'freeVar', name: 'q_0' } },
  ])
  return mkDiagramWithBoundary(b.build(), [wq])
}
