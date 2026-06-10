import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../../src/kernel/term/parse'
import { mkDiagram, DiagramError, type Region, type DiagramNode, type Wire } from '../../../src/kernel/diagram/diagram'

const noConsts = new Set<string>()
const p = (s: string) => parseTerm(s, noConsts)

const sheet: Record<string, Region> = { r0: { kind: 'sheet' } }

describe('mkDiagram rejections', () => {
  it('rejects a missing root', () => {
    expect(() => mkDiagram({ root: 'nope', regions: sheet }))
      .toThrowError(/root region 'nope' does not exist/)
  })

  it('rejects a non-sheet root', () => {
    expect(() => mkDiagram({
      root: 'r1',
      regions: { r0: { kind: 'sheet' }, r1: { kind: 'cut', parent: 'r0' } },
    })).toThrowError(/root region 'r1' must be a sheet/)
  })

  it('rejects a second sheet', () => {
    expect(() => mkDiagram({
      root: 'r0',
      regions: { r0: { kind: 'sheet' }, r1: { kind: 'sheet' } },
    })).toThrowError(/second sheet/)
  })

  it('rejects negative, fractional, and unsafely large bubble arity', () => {
    expect(() => mkDiagram({
      root: 'r0',
      regions: { r0: { kind: 'sheet' }, r1: { kind: 'bubble', parent: 'r0', arity: -1 } },
    })).toThrowError(/arity must be a non-negative safe integer/)
    expect(() => mkDiagram({
      root: 'r0',
      regions: { r0: { kind: 'sheet' }, r1: { kind: 'bubble', parent: 'r0', arity: 1.5 } },
    })).toThrowError(/arity must be a non-negative safe integer/)
    expect(() => mkDiagram({
      root: 'r0',
      regions: { r0: { kind: 'sheet' }, r1: { kind: 'bubble', parent: 'r0', arity: 2 ** 53 } },
    })).toThrowError(/arity must be a non-negative safe integer/)
  })

  it('rejects a missing parent', () => {
    expect(() => mkDiagram({
      root: 'r0',
      regions: { r0: { kind: 'sheet' }, r1: { kind: 'cut', parent: 'ghost' } },
    })).toThrowError(/missing parent 'ghost'/)
  })

  it('rejects a parent cycle', () => {
    expect(() => mkDiagram({
      root: 'r0',
      regions: {
        r0: { kind: 'sheet' },
        r1: { kind: 'cut', parent: 'r2' },
        r2: { kind: 'cut', parent: 'r1' },
      },
    })).toThrowError(/cycle/)
  })

  it('rejects a node in a missing region', () => {
    expect(() => mkDiagram({
      root: 'r0', regions: sheet,
      nodes: { n0: { kind: 'term', region: 'ghost', term: p('\\x. x') } },
    })).toThrowError(/node 'n0' is in missing region 'ghost'/)
  })

  it('rejects an atom whose binder is missing, not a bubble, or not enclosing', () => {
    const base: Record<string, Region> = {
      r0: { kind: 'sheet' },
      r1: { kind: 'bubble', parent: 'r0', arity: 0 },
      r2: { kind: 'cut', parent: 'r0' },
    }
    expect(() => mkDiagram({
      root: 'r0', regions: base,
      nodes: { n0: { kind: 'atom', region: 'r1', binder: 'ghost' } },
    })).toThrowError(/missing binder 'ghost'/)
    expect(() => mkDiagram({
      root: 'r0', regions: base,
      nodes: { n0: { kind: 'atom', region: 'r2', binder: 'r2' } },
    })).toThrowError(/must be a bubble/)
    // binder exists and is a bubble, but the atom sits outside it
    expect(() => mkDiagram({
      root: 'r0', regions: base,
      nodes: { n0: { kind: 'atom', region: 'r2', binder: 'r1' } },
    })).toThrowError(/must lie inside its binder/)
  })

  const oneNode = (wires: Record<string, Wire>) => {
    const nodes: Record<string, DiagramNode> = { n0: { kind: 'term', region: 'r0', term: p('\\x. x') } }
    return mkDiagram({ root: 'r0', regions: sheet, nodes, wires })
  }

  it('rejects a wire with a missing scope', () => {
    expect(() => oneNode({ w0: { scope: 'ghost', endpoints: [{ node: 'n0', port: { kind: 'output' } }] } }))
      .toThrowError(/missing scope region 'ghost'/)
  })

  it('rejects an endpoint on a missing node', () => {
    expect(() => oneNode({ w0: { scope: 'r0', endpoints: [{ node: 'ghost', port: { kind: 'output' } }] } }))
      .toThrowError(/missing node 'ghost'/)
  })

  it('rejects an endpoint on a non-existent port', () => {
    expect(() => oneNode({
      w0: { scope: 'r0', endpoints: [{ node: 'n0', port: { kind: 'freeVar', name: 'zz' } }] },
    })).toThrowError(/non-existent port 'v:zz'/)
  })

  it('rejects a port attached to two wires', () => {
    expect(() => oneNode({
      w0: { scope: 'r0', endpoints: [{ node: 'n0', port: { kind: 'output' } }] },
      w1: { scope: 'r0', endpoints: [{ node: 'n0', port: { kind: 'output' } }] },
    })).toThrowError(/attached to two wires/)
  })

  it('rejects a duplicate endpoint within a single wire, naming the wire once', () => {
    expect(() => oneNode({
      w0: {
        scope: 'r0',
        endpoints: [
          { node: 'n0', port: { kind: 'output' } },
          { node: 'n0', port: { kind: 'output' } },
        ],
      },
    })).toThrowError(/appears more than once in wire 'w0'/)
  })

  it('rejects an unattached port (the partition invariant)', () => {
    expect(() => oneNode({})).toThrowError(/port 'out' of node 'n0' is not attached/)
  })

  it('rejects a wire whose scope does not enclose an endpoint', () => {
    // node inside the sheet, wire scoped inside a cut that does not contain the node
    expect(() => mkDiagram({
      root: 'r0',
      regions: { r0: { kind: 'sheet' }, r1: { kind: 'cut', parent: 'r0' } },
      nodes: { n0: { kind: 'term', region: 'r0', term: p('\\x. x') } },
      wires: { w0: { scope: 'r1', endpoints: [{ node: 'n0', port: { kind: 'output' } }] } },
    })).toThrowError(/does not enclose node 'n0'/)
  })

  it('all rejections are DiagramError instances', () => {
    try {
      mkDiagram({ root: 'nope', regions: sheet })
      expect.unreachable('should have thrown')
    } catch (e) {
      expect(e).toBeInstanceOf(DiagramError)
    }
  })
})
