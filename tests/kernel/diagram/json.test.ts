import { describe, expect, it } from 'vitest'
import { mkDiagram } from '../../../src/kernel/diagram/diagram'
import {
  diagramFromJson,
  diagramToJson,
  parsePortKey,
  sigFromJson,
  sigToJson,
} from '../../../src/kernel/diagram/json'
import { exploreForm } from '../../../src/kernel/diagram/canonical/explore'
import { IOTA, relSig } from '../../../src/kernel/diagram/sig'
import { applyIdentification } from '../../../src/kernel/rules/identity-rules'

function sample() {
  const relation = relSig([IOTA])
  return mkDiagram({
    root: 'r0',
    regions: {
      r0: { kind: 'sheet' },
      r1: { kind: 'cut', parent: 'r0' },
    },
    nodes: {
      atom: { kind: 'atom', region: 'r1', sig: relation },
      ref: { kind: 'ref', region: 'r1', defId: 'P', sig: relation },
      eq: { kind: 'identity', region: 'r1', sig: IOTA, arity: 2 },
      relationPin: { kind: 'identity', region: 'r0', sig: relation, arity: 1 },
      otherPin: { kind: 'identity', region: 'r0', sig: IOTA, arity: 1 },
    },
    wires: {
      relation: {
        sig: relation,
        endpoints: [
          { node: 'atom', port: { kind: 'head' } },
          { node: 'relationPin', port: { kind: 'identity', index: 0 } },
        ],
      },
      value: {
        sig: IOTA,
        endpoints: [
          { node: 'atom', port: { kind: 'arg', index: 0 } },
          { node: 'ref', port: { kind: 'arg', index: 0 } },
          { node: 'eq', port: { kind: 'identity', index: 0 } },
        ],
      },
      other: {
        sig: IOTA,
        endpoints: [
          { node: 'eq', port: { kind: 'identity', index: 1 } },
          { node: 'otherPin', port: { kind: 'identity', index: 0 } },
        ],
      },
    },
  })
}

describe('diagram JSON', () => {
  it('round-trips all node kinds structurally and canonically', () => {
    const diagram = sample()
    const encoded = diagramToJson(diagram)
    const decoded = diagramFromJson(JSON.parse(JSON.stringify(encoded)))

    expect(decoded).toEqual(diagram)
    expect(exploreForm(decoded)).toBe(exploreForm(diagram))
    expect(diagramToJson(decoded)).toEqual(encoded)
  })

  it('serializes recursive signatures and identity port keys canonically', () => {
    const sig = relSig([IOTA, relSig([IOTA])])
    expect(sigToJson(sig)).toEqual({
      kind: 'rel',
      args: [
        { kind: 'iota' },
        { kind: 'rel', args: [{ kind: 'iota' }] },
      ],
    })
    expect(sigFromJson(JSON.parse(JSON.stringify(sigToJson(sig))), 'wire')).toEqual(sig)
    expect(parsePortKey('i:12')).toEqual({ kind: 'identity', index: 12 })
    expect(() => parsePortKey('i:1e2')).toThrowError(/unrecognized port key/)
  })

  it('rejects unknown fields and legacy node/port vocabulary', () => {
    const encoded = JSON.parse(JSON.stringify(diagramToJson(sample()))) as {
      nodes: Record<string, Record<string, unknown>>
      wires: Record<string, { endpoints: { port: string }[] }>
    }
    encoded.nodes.ref!['layout'] = {}
    expect(() => diagramFromJson(encoded)).toThrowError(/unknown field 'layout'/)

    const legacyNode = JSON.parse(JSON.stringify(diagramToJson(sample()))) as {
      nodes: Record<string, unknown>
    }
    legacyNode.nodes.ref = { kind: 'term', region: 'r1', term: '#0' }
    expect(() => diagramFromJson(legacyNode)).toThrowError(/unrecognized shape/)

    const legacyPort = JSON.parse(JSON.stringify(diagramToJson(sample()))) as {
      wires: Record<string, { endpoints: { port: string }[] }>
    }
    legacyPort.wires.value!.endpoints[0]!.port = 'out'
    expect(() => diagramFromJson(legacyPort)).toThrowError(/unrecognized port key 'out'/)
  })

  it('revalidates decoded diagrams', () => {
    const encoded = JSON.parse(JSON.stringify(diagramToJson(sample()))) as {
      nodes: Record<string, { region: string }>
    }
    encoded.nodes.ref!.region = 'ghost'
    expect(() => diagramFromJson(encoded)).toThrowError(/missing region 'ghost'/)
  })

  it('rejects malformed top-level and signature structures', () => {
    expect(() => diagramFromJson(null)).toThrowError(/top level/)
    expect(() => diagramFromJson({ root: 'r0' })).toThrowError(/must be objects/)
    expect(() => sigFromJson({ kind: 'term' }, 'wire'))
      .toThrowError(/kind.*iota.*rel/)
    expect(() => sigFromJson({ kind: 'iota', extra: true }, 'wire'))
      .toThrowError(/extra fields/)
  })

  it('decodes a co-scoped identity without collapsing it', () => {
    const decoded = diagramFromJson({
      root: 'r0',
      regions: { r0: { kind: 'sheet' } },
      nodes: {
        eq: {
          kind: 'identity',
          region: 'r0',
          sig: { kind: 'iota' },
          arity: 2,
        },
        leftPin: { kind: 'identity', region: 'r0', sig: { kind: 'iota' }, arity: 1 },
        rightPin: { kind: 'identity', region: 'r0', sig: { kind: 'iota' }, arity: 1 },
      },
      wires: {
        left: {
          sig: { kind: 'iota' },
          endpoints: [{ node: 'eq', port: 'i:0' }, { node: 'leftPin', port: 'i:0' }],
        },
        right: {
          sig: { kind: 'iota' },
          endpoints: [{ node: 'eq', port: 'i:1' }, { node: 'rightPin', port: 'i:0' }],
        },
      },
    })

    // Decoding is validate-and-freeze: the file says the two lines are equal
    // at the root, and that is what the diagram holds. Merging them is a
    // recorded identification step, never a side effect of reading a file.
    expect(decoded.nodes.eq).toEqual({
      kind: 'identity',
      region: 'r0',
      sig: IOTA,
      arity: 2,
    })
    expect(Object.keys(decoded.wires).sort()).toEqual(['left', 'right'])

    const collapsed = applyIdentification(decoded, {
      kind: 'collapse',
      node: 'eq',
      survivor: 'left',
      absorbed: ['right'],
    })
    expect(Object.keys(collapsed.wires)).toEqual(['left'])
    expect(collapsed.nodes.eq).toEqual({
      kind: 'identity',
      region: 'r0',
      sig: IOTA,
      arity: 1,
    })
  })
})
