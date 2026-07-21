import { describe, expect, it } from 'vitest'
import { parseTerm } from '../../src/kernel/term/parse'
import { proofTermSpawnStep } from '../../src/app/interact/proof-spawn'

describe('closed-term proof spawning', () => {
  it('constructs the replayable proof step from a closed source term', () => {
    expect(proofTermSpawnStep('\\x. x', 'r7')).toEqual({
      rule: 'closedTermIntro',
      region: 'r7',
      term: parseTerm('\\x. x'),
    })
  })

  it('dispatches open source terms to the polarity-gated atomic rule', () => {
    expect(proofTermSpawnStep('x', 'r7')).toEqual({
      rule: 'openTermSpawn',
      region: 'r7',
      term: parseTerm('x'),
      freePorts: ['x'],
    })
  })
})
