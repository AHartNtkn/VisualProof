import { describe, expect, it } from 'vitest'
import { FeedbackController } from '../../src/app/feedback'

describe('FeedbackController — error-only authority', () => {
  it('keeps only the newest pointer-local refusal', () => {
    const feedback = new FeedbackController(() => 100)
    const first = feedback.refuse({ text: 'first refusal', pointer: { x: 10, y: 20 } })
    const latest = feedback.refuse({ text: 'second refusal', pointer: { x: 30, y: 40 } })

    expect(latest.sequence).toBe(first.sequence + 1)
    expect(latest.expiresAt).toBe(3_300)
    expect(feedback.snapshot().refusal).toEqual(latest)
  })

  it('does not let an old expiry clear a newer refusal', () => {
    const feedback = new FeedbackController(() => 100)
    const old = feedback.refuse({ text: 'old', pointer: { x: 1, y: 2 } })
    feedback.refuse({ text: 'new', pointer: { x: 3, y: 4 } })

    feedback.clearRefusal(old.sequence)

    expect(feedback.snapshot().refusal?.text).toBe('new')
  })

  it('clears the current refusal by identity or unconditionally', () => {
    const feedback = new FeedbackController()
    const refusal = feedback.refuse({ text: 'no', pointer: { x: 5, y: 6 } })
    feedback.clearRefusal(refusal.sequence)
    expect(feedback.snapshot().refusal).toBeNull()

    feedback.refuse({ text: 'again', pointer: { x: 7, y: 8 } })
    feedback.clearRefusal()
    expect(feedback.snapshot().refusal).toBeNull()
  })

  it('owns stable field problems independently of transient refusals', () => {
    const feedback = new FeedbackController()
    feedback.setProblem('bubble-arity', "'-1' is not a valid arity")
    feedback.refuse({ text: 'unrelated refusal', pointer: { x: 9, y: 10 } })

    expect(feedback.snapshot().problems).toEqual([
      { id: 'bubble-arity', text: "'-1' is not a valid arity" },
    ])
    feedback.clearProblem('bubble-arity')
    expect(feedback.snapshot().problems).toEqual([])
    expect(feedback.snapshot().refusal?.text).toBe('unrelated refusal')
  })

  it('replaces a field problem in place without creating an event history', () => {
    const feedback = new FeedbackController()
    feedback.setProblem('bubble-arity', 'first')
    feedback.setProblem('bubble-arity', 'corrected detail')

    expect(feedback.snapshot().problems).toEqual([
      { id: 'bubble-arity', text: 'corrected detail' },
    ])
  })
})
