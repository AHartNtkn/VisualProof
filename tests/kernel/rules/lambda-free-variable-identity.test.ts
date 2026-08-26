import { describe, expect, it } from 'vitest'
import { sameDiagram } from '../../../src/kernel/diagram/canonical/iso'
import { mkDiagram, type Diagram, type Wire } from '../../../src/kernel/diagram/diagram'
import { IOTA, relSig, type Sig } from '../../../src/kernel/diagram/sig'
import { wireAt } from '../../../src/kernel/rules/access'
import { applyFreeVariableIdentity } from '../../../src/kernel/rules/lambda/free-variable-identity'
import { application, bound, free, lambda, type Term } from '../../../src/kernel/term/term'

function freeTermDiagram(
  term: Term = free(0),
  repeatedWire = false,
): Diagram {
  const nodes = repeatedWire ? {
    term: { kind: 'term' as const, region: 'root', term, freeArity: 1 },
  } : {
    term: { kind: 'term' as const, region: 'root', term, freeArity: 1 },
    outPin: { kind: 'identity' as const, region: 'root', sig: IOTA, arity: 1 },
    freePin: { kind: 'identity' as const, region: 'root', sig: IOTA, arity: 1 },
  }
  const wires: Record<string, Wire> = repeatedWire
    ? {
        value: {
          sig: IOTA,
          endpoints: [
            { node: 'term', port: { kind: 'output' } },
            { node: 'term', port: { kind: 'free', index: 0 } },
          ],
        },
      }
    : {
        output: {
          sig: IOTA,
          endpoints: [
            { node: 'term', port: { kind: 'output' } },
            { node: 'outPin', port: { kind: 'identity', index: 0 } },
          ],
        },
        free: {
          sig: IOTA,
          endpoints: [
            { node: 'term', port: { kind: 'free', index: 0 } },
            { node: 'freePin', port: { kind: 'identity', index: 0 } },
          ],
        },
      }
  return mkDiagram({ root: 'root', regions: { root: { kind: 'sheet' } }, nodes, wires })
}

function identityDiagram(sig: Sig, arity: number): Diagram {
  const nodes = {
    identity: { kind: 'identity' as const, region: 'root', sig, arity },
    ...Object.fromEntries(Array.from({ length: arity }, (_, index) => [
      `pin${index}`,
      { kind: 'identity' as const, region: 'root', sig, arity: 1 },
    ])),
  }
  const wires = Object.fromEntries(Array.from({ length: arity }, (_, index) => [
    `wire${index}`,
    {
      sig,
      endpoints: [
        { node: 'identity', port: { kind: 'identity' as const, index } },
        { node: `pin${index}`, port: { kind: 'identity' as const, index: 0 } },
      ],
    },
  ]))
  return mkDiagram({ root: 'root', regions: { root: { kind: 'sheet' } }, nodes, wires })
}

describe('applyFreeVariableIdentity', () => {
  it('round-trips a free-slot term node through binary IOTA identity', () => {
    const source = freeTermDiagram()
    const asIdentity = applyFreeVariableIdentity(source, {
      direction: 'toIdentity', node: 'term',
    })
    expect(asIdentity.nodes.term?.kind).toBe('identity')
    const restored = applyFreeVariableIdentity(asIdentity, {
      direction: 'toTerm', node: 'term', outputPort: 0,
    })
    expect(sameDiagram(restored, source)).toBe(true)
  })

  it('supports both reverse output orientations', () => {
    const source = identityDiagram(IOTA, 2)
    const outputFirst = applyFreeVariableIdentity(source, {
      direction: 'toTerm', node: 'identity', outputPort: 0,
    })
    const outputSecond = applyFreeVariableIdentity(source, {
      direction: 'toTerm', node: 'identity', outputPort: 1,
    })

    expect(wireAt(outputFirst, 'identity', { kind: 'output' })).toBe('wire0')
    expect(wireAt(outputFirst, 'identity', { kind: 'free', index: 0 })).toBe('wire1')
    expect(wireAt(outputSecond, 'identity', { kind: 'output' })).toBe('wire1')
    expect(wireAt(outputSecond, 'identity', { kind: 'free', index: 0 })).toBe('wire0')
  })

  it('preserves repeated-wire incidences in both directions', () => {
    const source = freeTermDiagram(free(0), true)
    const identity = applyFreeVariableIdentity(source, {
      direction: 'toIdentity', node: 'term',
    })
    expect(identity.wires.value?.endpoints).toEqual([
      { node: 'term', port: { kind: 'identity', index: 0 } },
      { node: 'term', port: { kind: 'identity', index: 1 } },
    ])
    const restored = applyFreeVariableIdentity(identity, {
      direction: 'toTerm', node: 'term', outputPort: 1,
    })
    expect(restored.wires.value?.endpoints).toEqual([
      { node: 'term', port: { kind: 'free', index: 0 } },
      { node: 'term', port: { kind: 'output' } },
    ])
  })

  it('refuses non-IOTA and nonbinary identities', () => {
    expect(() => applyFreeVariableIdentity(identityDiagram(relSig([]), 2), {
      direction: 'toTerm', node: 'identity', outputPort: 0,
    })).toThrowError(/IOTA/i)
    expect(() => applyFreeVariableIdentity(identityDiagram(IOTA, 1), {
      direction: 'toTerm', node: 'identity', outputPort: 0,
    })).toThrowError(/binary/i)
  })

  it('refuses term nodes not containing only free slot zero', () => {
    const source = freeTermDiagram(application(lambda(bound(0)), free(0)))
    expect(() => applyFreeVariableIdentity(source, {
      direction: 'toIdentity', node: 'term',
    })).toThrowError(/free slot 0/i)
  })
})
