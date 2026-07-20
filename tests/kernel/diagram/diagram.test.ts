import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../../src/kernel/term/parse'
import {
  mkDiagram, portKey, requiredPorts, DiagramError,
  type Region, type DiagramNode, type DiagramNodeInput, type Wire,
} from '../../../src/kernel/diagram/diagram'

const p = (s: string) => parseTerm(s)

describe('portKey', () => {
  it('produces distinct keys for the three port kinds', () => {
    expect(portKey({ kind: 'output' })).toBe('out')
    expect(portKey({ kind: 'freeVar', name: 'y' })).toBe('v:y')
    expect(portKey({ kind: 'arg', index: 2 })).toBe('a:2')
  })
})

describe('requiredPorts', () => {
  it('gives output plus one freeVar port per distinct free variable, in first-occurrence order', () => {
    const regions: Record<string, Region> = { r0: { kind: 'sheet' } }
    const node: DiagramNode = {
      kind: 'term', region: 'r0', term: p('\\x. y (z y x)'), freePorts: ['y', 'z'],
    }
    expect(requiredPorts({ regions }, node).map(portKey)).toEqual(['out', 'v:y', 'v:z'])
  })

  it('gives arg ports 0..arity-1 for atoms, read from the binder bubble', () => {
    const regions: Record<string, Region> = {
      r0: { kind: 'sheet' },
      r1: { kind: 'bubble', parent: 'r0', arity: 2 },
    }
    const node: DiagramNode = { kind: 'atom', region: 'r1', binder: 'r1' }
    expect(requiredPorts({ regions }, node).map(portKey)).toEqual(['a:0', 'a:1'])
  })

  it('throws when an atom binder is not a bubble (public API error surface)', () => {
    const regions: Record<string, Region> = { r0: { kind: 'sheet' } }
    const node: DiagramNode = { kind: 'atom', region: 'r0', binder: 'r0' }
    expect(() => requiredPorts({ regions }, node)).toThrowError(/atom binder 'r0' is not a bubble/)
  })
})

describe('mkDiagram (happy path)', () => {
  it('constructs a valid diagram: bubble with one atom, a term node feeding both args', () => {
    // sheet > bubble(arity 2) containing atom X(t, t) where t is the output of \x.x
    const regions: Record<string, Region> = {
      r0: { kind: 'sheet' },
      r1: { kind: 'bubble', parent: 'r0', arity: 2 },
    }
    const nodes: Record<string, DiagramNodeInput> = {
      n0: { kind: 'term', region: 'r1', term: p('\\x. x') },
      n1: { kind: 'atom', region: 'r1', binder: 'r1' },
    }
    const wires: Record<string, Wire> = {
      w0: {
        scope: 'r1',
        endpoints: [
          { node: 'n0', port: { kind: 'output' } },
          { node: 'n1', port: { kind: 'arg', index: 0 } },
          { node: 'n1', port: { kind: 'arg', index: 1 } },
        ],
      },
    }
    const d = mkDiagram({ root: 'r0', regions, nodes, wires })
    expect(d.root).toBe('r0')
    expect(Object.keys(d.regions)).toHaveLength(2)
    expect(Object.isFrozen(d)).toBe(true)
    expect(Object.isFrozen(d.nodes)).toBe(true)
  })

  it('accepts wires with zero endpoints (bare existence) and zero-arity bubbles', () => {
    const d = mkDiagram({
      root: 'r0',
      regions: { r0: { kind: 'sheet' }, r1: { kind: 'bubble', parent: 'r0', arity: 0 } },
      wires: { w0: { scope: 'r1', endpoints: [] } },
    })
    expect(d.wires['w0']?.endpoints).toHaveLength(0)
  })

  it('does not alias ports across node-id/port-name boundaries (separator safety)', () => {
    // node id "n0 v:x" with output, plus node "n0" with free var "x out":
    // a naive string key `${node} ${port}` collides; both must coexist.
    const regions: Record<string, Region> = { r0: { kind: 'sheet' } }
    const nodes: Record<string, DiagramNodeInput> = {
      'n0': { kind: 'term', region: 'r0', term: { kind: 'port' as const, name: 'x out' } },
      'n0 v:x': { kind: 'term', region: 'r0', term: p('\\x. x') },
    }
    const wires: Record<string, Wire> = {
      w0: { scope: 'r0', endpoints: [{ node: 'n0', port: { kind: 'output' } }] },
      w1: { scope: 'r0', endpoints: [{ node: 'n0', port: { kind: 'freeVar', name: 'x out' } }] },
      w2: { scope: 'r0', endpoints: [{ node: 'n0 v:x', port: { kind: 'output' } }] },
    }
    expect(() => mkDiagram({ root: 'r0', regions, nodes, wires })).not.toThrow()
  })

  it('accepts a wire scoped above its endpoints (line of identity reaching into a cut)', () => {
    const regions: Record<string, Region> = {
      r0: { kind: 'sheet' },
      r1: { kind: 'cut', parent: 'r0' },
    }
    const nodes: Record<string, DiagramNodeInput> = {
      n0: { kind: 'term', region: 'r0', term: p('\\x. x') },
      n1: { kind: 'term', region: 'r1', term: p('\\x. x') },
    }
    const wires: Record<string, Wire> = {
      w0: {
        scope: 'r0',
        endpoints: [
          { node: 'n0', port: { kind: 'output' } },
          { node: 'n1', port: { kind: 'output' } },
        ],
      },
    }
    expect(() => mkDiagram({ root: 'r0', regions, nodes, wires })).not.toThrow()
  })
})

describe('DiagramError', () => {
  it('is a distinct error class', () => {
    expect(new DiagramError('x')).toBeInstanceOf(Error)
    expect(new DiagramError('x').name).toBe('DiagramError')
  })
})
