import { describe, expect, it } from 'vitest'
import {
  DiagramError,
  mkDiagram,
  type DiagramNode,
  type Region,
  type Wire,
} from '../../../src/kernel/diagram/diagram'
import { IOTA, relSig } from '../../../src/kernel/diagram/sig'

const sheet: Record<string, Region> = { r0: { kind: 'sheet' } }
const refNode: DiagramNode = {
  kind: 'ref',
  region: 'r0',
  defId: 'P',
  sig: relSig([IOTA]),
}

function oneRef(wires: Record<string, Wire>) {
  return mkDiagram({
    root: 'r0',
    regions: sheet,
    nodes: { n0: refNode },
    wires,
  })
}

describe('mkDiagram validation', () => {
  it('rejects invalid roots, second sheets, missing parents, and cycles', () => {
    expect(() => mkDiagram({ root: 'missing', regions: sheet }))
      .toThrowError(/root region 'missing' does not exist/)
    expect(() => mkDiagram({
      root: 'r1',
      regions: { ...sheet, r1: { kind: 'cut', parent: 'r0' } },
    })).toThrowError(/must be a sheet/)
    expect(() => mkDiagram({
      root: 'r0',
      regions: { ...sheet, r1: { kind: 'sheet' } },
    })).toThrowError(/second sheet/)
    expect(() => mkDiagram({
      root: 'r0',
      regions: { ...sheet, r1: { kind: 'cut', parent: 'ghost' } },
    })).toThrowError(/missing parent 'ghost'/)
    expect(() => mkDiagram({
      root: 'r0',
      regions: {
        ...sheet,
        r1: { kind: 'cut', parent: 'r2' },
        r2: { kind: 'cut', parent: 'r1' },
      },
    })).toThrowError(/cycle/)
  })

  it('rejects nodes in missing regions and malformed node signatures', () => {
    expect(() => mkDiagram({
      root: 'r0',
      regions: sheet,
      nodes: {
        n0: { kind: 'ref', region: 'ghost', defId: 'P', sig: relSig([]) },
      },
    })).toThrowError(/node 'n0' is in missing region 'ghost'/)
    expect(() => mkDiagram({
      root: 'r0',
      regions: sheet,
      nodes: {
        n0: { kind: 'atom', region: 'r0', sig: IOTA as never },
      },
    })).toThrowError(/must be a relation signature/)
    expect(() => mkDiagram({
      root: 'r0',
      regions: sheet,
      nodes: {
        n0: {
          kind: 'identity',
          region: 'r0',
          sig: { kind: 'bogus' } as never,
          arity: 2,
        },
      },
    })).toThrowError(/identity node 'n0' sig/)
  })

  it('rejects missing scopes, nodes, ports, duplicate attachments, and omissions', () => {
    expect(() => oneRef({
      w0: {
        scope: 'ghost',
        sig: IOTA,
        endpoints: [{ node: 'n0', port: { kind: 'arg', index: 0 } }],
      },
    })).toThrowError(/missing scope region 'ghost'/)
    expect(() => oneRef({
      w0: {
        scope: 'r0',
        sig: IOTA,
        endpoints: [{ node: 'ghost', port: { kind: 'arg', index: 0 } }],
      },
    })).toThrowError(/missing node 'ghost'/)
    expect(() => oneRef({
      w0: {
        scope: 'r0',
        sig: IOTA,
        endpoints: [{ node: 'n0', port: { kind: 'head' } }],
      },
    })).toThrowError(/non-existent port 'hd'/)
    expect(() => oneRef({
      w0: {
        scope: 'r0',
        sig: IOTA,
        endpoints: [
          { node: 'n0', port: { kind: 'arg', index: 0 } },
          { node: 'n0', port: { kind: 'arg', index: 0 } },
        ],
      },
    })).toThrowError(/appears more than once/)
    expect(() => oneRef({
      w0: {
        scope: 'r0',
        sig: IOTA,
        endpoints: [{ node: 'n0', port: { kind: 'arg', index: 0 } }],
      },
      w1: {
        scope: 'r0',
        sig: IOTA,
        endpoints: [{ node: 'n0', port: { kind: 'arg', index: 0 } }],
      },
    })).toThrowError(/attached to two wires/)
    expect(() => oneRef({})).toThrowError(/port 'a:0'.*not attached/)
  })

  it('rejects signature mismatch and a wire scope below its endpoint', () => {
    expect(() => oneRef({
      w0: {
        scope: 'r0',
        sig: relSig([]),
        endpoints: [{ node: 'n0', port: { kind: 'arg', index: 0 } }],
      },
    })).toThrowError(/does not match port 'a:0'/)
    expect(() => mkDiagram({
      root: 'r0',
      regions: {
        ...sheet,
        r1: { kind: 'cut', parent: 'r0' },
      },
      nodes: { n0: refNode },
      wires: {
        w0: {
          scope: 'r1',
          sig: IOTA,
          endpoints: [{ node: 'n0', port: { kind: 'arg', index: 0 } }],
        },
      },
    })).toThrowError(/does not enclose node 'n0'/)
  })

  it('rejects displaced term/body node vocabulary and throws DiagramError', () => {
    for (const node of [
      { kind: 'term', region: 'r0', term: {} },
      { kind: 'body', region: 'r0', content: {} },
    ]) {
      try {
        mkDiagram({
          root: 'r0',
          regions: sheet,
          nodes: { legacy: node as never },
        })
        expect.unreachable('legacy node should be rejected')
      } catch (error) {
        expect(error).toBeInstanceOf(DiagramError)
        expect((error as Error).message).toMatch(/unrecognized kind/)
      }
    }
  })
})
