import { describe, expect, it } from 'vitest'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { mkDiagramWithBoundary } from '../../../src/kernel/diagram/boundary'
import { stepFromJson, stepToJson } from '../../../src/kernel/proof/json'
import type { ProofStep } from '../../../src/kernel/proof/step'

function encodedStep(binders: unknown): Record<string, unknown> {
  const b = new DiagramBuilder()
  const encoded = stepToJson({
    rule: 'comprehensionInstantiate',
    bubble: 'host',
    comp: mkDiagramWithBoundary(b.build(), []),
    attachments: [],
    binders: [],
  }) as { comp: unknown }
  return {
    rule: 'comprehensionInstantiate',
    bubble: 'host',
    comp: encoded.comp,
    attachments: [],
    binders,
  }
}

describe('comprehension binder-pair proof JSON', () => {
  it('preserves exact pair order for integer-like and prototype-like pattern ids', () => {
    const b = new DiagramBuilder()
    const binders = [
      ['10', 'outer'],
      ['2', 'middle'],
      ['__proto__', 'inner'],
    ] as const
    const step: ProofStep = {
      rule: 'comprehensionInstantiate',
      bubble: 'host',
      comp: mkDiagramWithBoundary(b.build(), []),
      attachments: [],
      binders,
    }

    const json = stepToJson(step) as { binders: unknown }
    expect(json.binders).toEqual(binders)
    expect(stepFromJson(JSON.parse(JSON.stringify(json)))).toEqual(step)
  })

  it('rejects duplicate pattern ids', () => {
    expect(() => stepFromJson(encodedStep([
      ['stub', 'outer'],
      ['stub', 'inner'],
    ]))).toThrowError(/binders repeats pattern id 'stub'/)
  })

  it('rejects duplicate host targets', () => {
    expect(() => stepFromJson(encodedStep([
      ['outerStub', 'same'],
      ['innerStub', 'same'],
    ]))).toThrowError(/binders repeats host target 'same'/)
  })

  it('rejects malformed pairs and the obsolete record representation', () => {
    expect(() => stepFromJson(encodedStep([['stub']]))).toThrowError(/binders\[0\].*pair/)
    expect(() => stepFromJson(encodedStep({ stub: 'host' }))).toThrowError(/binders must be an array/)
  })
})
