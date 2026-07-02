// inCutNat (UPDATE 4): original canonical natRelation with w0's scope moved
// from root to rB. Not exists R exists w0 [Z(w0) ^ R(w0) ^ Cl(R) ^ not R(x)].
import { DiagramBuilder } from '../../../../../src/kernel/diagram/builder'
import type { Endpoint, NodeId, RegionId, WireId } from '../../../../../src/kernel/diagram/diagram'
import { p } from './lib4'

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
  const ny = b.termNode(cut2, p('SUCC s0'))
  b.wire(cut2, [
    { node: a1, port: { kind: 'arg', index: 0 } },
    { node: ny, port: { kind: 'freeVar', name: 's0' } },
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
