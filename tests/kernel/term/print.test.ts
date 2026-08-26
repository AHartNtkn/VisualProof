import { describe, expect, it } from 'vitest'
import { application, bound, free, lambda } from '../../../src/kernel/term/term'
import { printTerm } from '../../../src/kernel/term/print'

describe('printTerm', () => {
  it('prints binders outside-in and applications with minimal parentheses', () => {
    const churchTwo = lambda(lambda(application(bound(1), application(bound(1), bound(0)))))
    expect(printTerm(churchTwo)).toBe('\\x0. \\x1. x0 (x0 x1)')
    expect(printTerm(application(application(free(0), free(1)), free(2)), ['f', 'a', 'b']))
      .toBe('f a b')
    expect(printTerm(application(free(0), application(free(1), free(2))), ['f', 'g', 'a']))
      .toBe('f (g a)')
    expect(printTerm(application(lambda(bound(0)), free(0)), ['a'])).toBe('(\\x0. x0) a')
  })

  it('uses canonical free names when boundary spellings are absent', () => {
    expect(printTerm(application(free(0), free(2)))).toBe('f0 f2')
  })

  it('avoids binder collisions with supplied or canonical free names', () => {
    expect(printTerm(lambda(application(bound(0), free(0))), ['x0'])).toBe('\\_x0. _x0 x0')
  })

  it('rejects missing supplied names and malformed bound references', () => {
    expect(() => printTerm(free(1), ['onlySlotZero'])).toThrowError(/free slot 1.*identifier/i)
    expect(() => printTerm(bound(0))).toThrowError(/unbound de Bruijn index 0/i)
  })
})
