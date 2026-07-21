import { parseTerm } from '../../src/kernel/term/parse'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { mkSelection } from '../../src/kernel/diagram/subgraph/selection'
import { EMPTY_PROOF_CONTEXT, type ProofContext } from '../../src/kernel/proof/context'

const pc = (s: string) => parseTerm(s)

export const emptyCtx: ProofContext = EMPTY_PROOF_CONTEXT

/**
 * An asymmetric arity-2 body on the sheet: term node `y` in root and term node
 * `z` inside a cut, their outputs joined by one internal wire (kept in the
 * selection). The two crossing wires are `y`'s input (into a positive region)
 * and `z`'s input (into the cut) — structurally distinct, so the boundary ORDER
 * is observable in the canonical fingerprint. Selecting {tA} plus the whole cut
 * subtree gives exactly those two crossing wires.
 */
export function sheetBody() {
  const b = new DiagramBuilder()
  const tA = b.termNode(b.root, pc('y'))
  const c1 = b.cut(b.root)
  const tB = b.termNode(c1, pc('z'))
  const wOut = b.wire(b.root, [
    { node: tA, port: { kind: 'output' } },
    { node: tB, port: { kind: 'output' } },
  ])
  const wY = b.wire(b.root, [{ node: tA, port: { kind: 'freeVar', name: 'y' } }])
  const wZ = b.wire(b.root, [{ node: tB, port: { kind: 'freeVar', name: 'z' } }])
  const d = b.build()
  const sel = mkSelection(d, { region: b.root, regions: [c1], nodes: [tA], wires: [wOut] })
  return { d, sel, wOut, wY, wZ }
}
