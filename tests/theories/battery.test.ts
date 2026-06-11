import { describe, it, expect } from 'vitest'
import { buildFregeTheory } from '../../src/theories/frege'
import { buildLambdaTheory } from '../../src/theories/lambda'
import { theoryToJson, loadTheory } from '../../src/kernel/proof/store'
import { applyTheorem } from '../../src/kernel/proof/theorem'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { mkSelection } from '../../src/kernel/diagram/subgraph/selection'
import { parseTerm } from '../../src/kernel/term/parse'

const consts = new Set(['ZERO', 'SUCC', 'PLUS', 'ONE', 'TWO'])
const p = (s: string) => parseTerm(s, consts)

describe('bundled theories as shipped artifacts', () => {
  it('both load from their serialized form and apply in fresh hosts', () => {
    const { ctx } = loadTheory(JSON.parse(JSON.stringify(theoryToJson(buildFregeTheory()))))
    const zeroIsNat = ctx.theorems.get('zeroIsNat')!
    const h = new DiagramBuilder()
    const nz = h.termNode(h.root, p('ZERO'))
    const w = h.wire(h.root, [{ node: nz, port: { kind: 'output' } }])
    const d = h.build()
    const out = applyTheorem(d, zeroIsNat, {
      sel: mkSelection(d, { region: d.root, regions: [], nodes: [nz], wires: [] }),
      args: [w],
    }, 'forward')
    expect(Object.values(out.regions).some((r) => r.kind === 'bubble')).toBe(true)
    expect(() => loadTheory(JSON.parse(JSON.stringify(theoryToJson(buildLambdaTheory()))))).not.toThrow()
  })

  it('the succNat derivation stays 16 steps (compression drift pin)', () => {
    const succ = buildFregeTheory().theorems.find((t) => t.name === 'succNat')!
    expect(succ.steps).toHaveLength(16)
  })
})
