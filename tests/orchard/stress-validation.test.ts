import { describe, expect, it } from 'vitest'
import { assertStressResidency, type StressResidency } from '../../orchard/stress-validation'

const validGame: StressResidency = {
  mode: 'game',
  trees: 100,
  visible: 54,
  resident: 54,
  full: 15,
  representationErrors: 0,
  representationError: '',
}

describe('orchard stress residency validation', () => {
  it('rejects representation failures with the rendered detail', () => {
    expect(() => assertStressResidency({
      ...validGame,
      resident: 53,
      representationErrors: 1,
      representationError: "tree 'tree-0042' reduced representation failed: buffer allocation failed",
    })).toThrow("game 100 representation failures (1): tree 'tree-0042' reduced representation failed: buffer allocation failed")
  })

  it('requires every visible Game tree to be resident after settlement', () => {
    expect(() => assertStressResidency({ ...validGame, resident: 53 }))
      .toThrow('game 100 settled with 53 resident of 54 visible trees')
    expect(() => assertStressResidency(validGame)).not.toThrow()
  })

  it('requires Raw to keep every logical tree visible, resident, and full', () => {
    expect(() => assertStressResidency({
      ...validGame,
      mode: 'raw',
      visible: 100,
      resident: 100,
      full: 99,
    })).toThrow('raw 100 settled with visible=100, resident=100, full=99')
  })
})
