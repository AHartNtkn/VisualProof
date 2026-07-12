import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../src/kernel/term/parse'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { mkDiagramWithBoundary } from '../../src/kernel/diagram/boundary'
import { mkSelection } from '../../src/kernel/diagram/subgraph/selection'
import { loadTheory, theoryToJson } from '../../src/kernel/proof/store'
import { startSession, applyForward as applyForwardAction, currentSide, meet, assembleTheorem, adoptTheorem } from '../../src/app/session'
import { singleStepAction } from '../../src/kernel/proof/action'
import { sessionTheory } from '../../src/app/persist'
import { bootFixture } from './boot-fixture'

const p = (s: string) => parseTerm(s)

async function provenToy() {
  const boot = await bootFixture()
  const l = new DiagramBuilder()
  l.termNode(l.root, p('\\x. x'))
  const lhs = mkDiagramWithBoundary(l.build(), [])
  const r = new DiagramBuilder()
  const m = r.termNode(r.root, p('\\x. x'))
  const c1 = r.cut(r.root)
  r.cut(c1)
  void m
  const rhs = mkDiagramWithBoundary(r.build(), [])
  let s = startSession(lhs, rhs, boot.ctx)
  s = applyForwardAction(s, singleStepAction('introduce double cut', {
    rule: 'doubleCutIntro',
    sel: mkSelection(currentSide(s, 'forward'), { region: currentSide(s, 'forward').root, regions: [], nodes: [], wires: [] }),
  }))
  expect(meet(s)).toBe(true)
  return { s, boot }
}

describe('adoptTheorem', () => {
  it('a checked session result becomes citable in the session context', async () => {
    const { s } = await provenToy()
    const thm = assembleTheorem(s, 'toy')
    const s2 = adoptTheorem(s, thm)
    expect(s2.ctx.theorems.has('toy')).toBe(true)
    expect(s.ctx.theorems.has('toy')).toBe(false) // immutably extended
  })

  it('refuses duplicate names and unverifiable theorems loudly', async () => {
    const { s } = await provenToy()
    const thm = assembleTheorem(s, 'toy')
    const s2 = adoptTheorem(s, thm)
    expect(() => adoptTheorem(s2, thm)).toThrowError(/already names a theorem/)
    const forged = { ...thm, actions: [] }
    expect(() => adoptTheorem(s, forged)).toThrowError(/does not arrive/)
  })
})

describe('sessionTheory + the file road', () => {
  it('round-trips the live context (with an adopted theorem) through theory JSON', async () => {
    const { s, boot } = await provenToy()
    const s2 = adoptTheorem(s, assembleTheorem(s, 'toy'))
    const theory = sessionTheory(s2.ctx, { relations: boot.relations })
    const { ctx } = loadTheory(JSON.parse(JSON.stringify(theoryToJson(theory))))
    expect(ctx.theorems.has('toy')).toBe(true)
    expect(ctx.theorems.has('onePlusOne')).toBe(true)
  })

  it('preserves dependency order: adopted theorems come after what they cite', async () => {
    const { s, boot } = await provenToy()
    const s2 = adoptTheorem(s, assembleTheorem(s, 'toy'))
    const theory = sessionTheory(s2.ctx, { relations: boot.relations })
    const names = theory.theorems.map((t) => t.name)
    expect(names.indexOf('toy')).toBeGreaterThan(names.indexOf('onePlusOne'))
  })
})
