import { describe, it, expect } from 'vitest'
import { buildLambdaTheory } from '../../src/theories/lambda'
import { verifyTheory, theoryToJson, loadTheory } from '../../src/kernel/proof/store'

describe('the bundled λ demo theory', () => {
  it('verifies: 1+1=2 and the fixed-point theorem replay through their gates', () => {
    const theory = buildLambdaTheory()
    const ctx = verifyTheory(theory)
    expect([...ctx.theorems.keys()]).toEqual(['onePlusOne', 'fixedPoint'])
  })

  it('the fixed-point proof carries an explicit certificate (no fueled search at replay)', () => {
    const theory = buildLambdaTheory()
    const fix = theory.theorems.find((t) => t.name === 'fixedPoint')!
    const conv = fix.steps.find((s) => s.rule === 'conversion')
    expect(conv).toBeDefined()
    expect(conv!.rule === 'conversion' && conv!.certificate.leftSteps.length).toBeGreaterThan(0)
  })

  it('round-trips through the file format', () => {
    const text = JSON.stringify(theoryToJson(buildLambdaTheory()))
    const { ctx } = loadTheory(JSON.parse(text))
    expect(ctx.theorems.size).toBe(2)
  })
})
