import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../../src/kernel/term/parse'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { DiagramError } from '../../../src/kernel/diagram/diagram'
import { mkSelection } from '../../../src/kernel/diagram/subgraph/selection'
import { RuleError } from '../../../src/kernel/rules/error'
import { applyWireJoin } from '../../../src/kernel/rules/wire-join'
import { applyOpenTermSpawn } from '../../../src/kernel/rules/spawn'
import { applyErasure, applyWireSever } from '../../../src/kernel/rules/erasure'
import { applyIteration } from '../../../src/kernel/rules/iteration'
import { applyDoubleCutElim } from '../../../src/kernel/rules/doublecut'

const p = (s: string) => parseTerm(s)

function caughtBy(f: () => unknown): unknown {
  try {
    f()
  } catch (e) {
    return e
  }
  throw new Error('expected the call to throw')
}

/**
 * The vocabulary invariant: RuleError fires iff a rule evaluated its gate
 * against a real referent and refused. A stale or unknown id is malformed
 * input — structural DiagramError — no matter which entry point receives it.
 */
describe('error vocabulary: unknown ids are DiagramError, gate refusals are RuleError', () => {
  it('atomic spawning with an unknown region throws DiagramError', () => {
    const h = new DiagramBuilder()
    h.cut(h.root)
    const d = h.build()
    expect(caughtBy(() => applyOpenTermSpawn(d, 'ghost', p('x'), ['x']))).toBeInstanceOf(DiagramError)
  })

  it('applyWireJoin with unknown wires throws DiagramError, in either position', () => {
    const h = new DiagramBuilder()
    const cut = h.cut(h.root)
    const n = h.termNode(cut, p('\\x. x'))
    const w = h.wire(cut, [{ node: n, port: { kind: 'output' } }])
    const d = h.build()
    expect(caughtBy(() => applyWireJoin(d, 'ghost', w))).toBeInstanceOf(DiagramError)
    expect(caughtBy(() => applyWireJoin(d, w, 'ghost'))).toBeInstanceOf(DiagramError)
    // even when both ids are the same unknown id: existence is checked before
    // the self-join gate, so no RuleError fires without a real referent
    expect(caughtBy(() => applyWireJoin(d, 'ghost', 'ghost'))).toBeInstanceOf(DiagramError)
  })

  it('applyErasure with a stale selection throws DiagramError', () => {
    const h1 = new DiagramBuilder()
    const cut = h1.cut(h1.root)
    h1.cut(cut)
    const n = h1.termNode(cut, p('\\x. x'))
    const d1 = h1.build()
    const sel = mkSelection(d1, { region: cut, regions: [], nodes: [n], wires: [] })
    const d2 = new DiagramBuilder().build() // no such region here
    expect(caughtBy(() => applyErasure(d2, sel))).toBeInstanceOf(DiagramError)
  })

  it('applyWireSever with an unknown wire throws DiagramError', () => {
    const d = new DiagramBuilder().build()
    expect(caughtBy(() => applyWireSever(d, 'ghost', []))).toBeInstanceOf(DiagramError)
  })

  it('applyIteration with an unknown target region throws DiagramError', () => {
    const h = new DiagramBuilder()
    const n = h.termNode(h.root, p('\\x. x'))
    const d = h.build()
    const sel = mkSelection(d, { region: d.root, regions: [], nodes: [n], wires: [] })
    expect(caughtBy(() => applyIteration(d, sel, 'ghost'))).toBeInstanceOf(DiagramError)
  })

  it('applyDoubleCutElim with an unknown region throws DiagramError', () => {
    const d = new DiagramBuilder().build()
    expect(caughtBy(() => applyDoubleCutElim(d, 'ghost'))).toBeInstanceOf(DiagramError)
  })

  it('gate refusals on real referents remain RuleError', () => {
    const h = new DiagramBuilder()
    const cut = h.cut(h.root)
    const n = h.termNode(cut, p('\\x. x'))
    const d = h.build()
    // atomic spawn at the positive root: a real region, refused by the gate
    expect(caughtBy(() => applyOpenTermSpawn(d, d.root, p('x'), ['x']))).toBeInstanceOf(RuleError)
    // erasure at a negative region: a real region, refused by the gate
    const sel = mkSelection(d, { region: cut, regions: [], nodes: [n], wires: [] })
    expect(caughtBy(() => applyErasure(d, sel))).toBeInstanceOf(RuleError)
  })
})
