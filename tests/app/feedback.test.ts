import { describe, expect, it } from 'vitest'
import { FeedbackController } from '../../src/app/feedback'

describe('FeedbackController', () => {
  it('keeps one typed current authority and monotonically identifies updates', () => {
    const feedback = new FeedbackController()
    const first = feedback.report({
      kind: 'guidance',
      text: 'release on another line to join',
      owner: { kind: 'viewport' },
      persistence: 'interaction',
    })
    const second = feedback.report({
      kind: 'success',
      text: 'lines joined',
      owner: { kind: 'viewport' },
      persistence: 'transient',
    })
    expect(second.sequence).toBe(first.sequence + 1)
    expect(feedback.snapshot().current).toEqual(second)
  })

  it('keeps unresolved problems independently of later transient results', () => {
    const feedback = new FeedbackController()
    const problem = feedback.report({
      kind: 'problem',
      text: "'-1' is not a valid arity",
      owner: { kind: 'control', id: 'bubble-arity' },
      persistence: 'problem',
      problemId: 'bubble-arity',
    })
    feedback.report({
      kind: 'success',
      text: 'term placed',
      owner: { kind: 'viewport' },
      persistence: 'transient',
    })
    expect(feedback.snapshot().problems).toEqual([problem])
    feedback.clearProblem('bubble-arity')
    expect(feedback.snapshot().problems).toEqual([])
  })

  it('clears active guidance without clearing a durable problem', () => {
    const feedback = new FeedbackController()
    feedback.report({
      kind: 'problem',
      text: 'save permission was revoked',
      owner: { kind: 'control', id: 'save' },
      persistence: 'problem',
      problemId: 'save',
    })
    feedback.report({
      kind: 'guidance',
      text: 'release Ctrl before pointer-up to pin',
      owner: { kind: 'node', id: 'n1' },
      persistence: 'interaction',
    })
    feedback.clearInteraction()
    expect(feedback.snapshot()).toMatchObject({ current: null, problems: [{ problemId: 'save' }] })
  })

  it('rejects problem identities on transient feedback and missing identities on problems', () => {
    const feedback = new FeedbackController()
    expect(() => feedback.report({
      kind: 'problem',
      text: 'broken',
      owner: { kind: 'viewport' },
      persistence: 'problem',
    })).toThrow('persistent feedback requires a stable problemId')
    expect(() => feedback.report({
      kind: 'success',
      text: 'done',
      owner: { kind: 'viewport' },
      persistence: 'transient',
      problemId: 'wrong',
    })).toThrow('only persistent feedback may carry a problemId')
  })
})
