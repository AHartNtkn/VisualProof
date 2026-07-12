import { describe, expect, it } from 'vitest'
import { parseTerm } from '../../src/kernel/term/parse'
import { closedTermIntroStep } from '../../src/app/interact/closed-term-intro'

describe('closed-term proof spawning', () => {
  it('constructs the replayable proof step from a closed source term', () => {
    expect(closedTermIntroStep('\\x. x', 'r7')).toEqual({
      rule: 'closedTermIntro',
      region: 'r7',
      term: parseTerm('\\x. x'),
    })
  })

  it('refuses an open source term before proof commit', () => {
    expect(() => closedTermIntroStep('x', 'r7'))
      .toThrow("closed-term introduction requires a closed term; free ports ['x'] remain")
  })
})
