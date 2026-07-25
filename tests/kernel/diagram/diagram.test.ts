import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../../src/kernel/term/parse'
import {
  mkDiagram, portKey, requiredPorts, portSig, DiagramError,
  type Region, type DiagramNode, type DiagramNodeInput, type Wire,
} from '../../../src/kernel/diagram/diagram'
import { mkDiagramWithBoundary } from '../../../src/kernel/diagram/boundary'
import { IOTA, relSig, sigKey } from '../../../src/kernel/diagram/sig'

const p = (s: string) => parseTerm(s)

describe('portKey', () => {
  it('produces distinct keys for the four port kinds', () => {
    expect(portKey({ kind: 'output' })).toBe('out')
    expect(portKey({ kind: 'freeVar', name: 'y' })).toBe('v:y')
    expect(portKey({ kind: 'arg', index: 2 })).toBe('a:2')
    expect(portKey({ kind: 'head' })).toBe('hd')
  })
})

describe('requiredPorts', () => {
  it('gives output plus one freeVar port per distinct free variable, in first-occurrence order', () => {
    const node: DiagramNode = {
      kind: 'term', region: 'r0', term: p('\\x. y (z y x)'), freePorts: ['y', 'z'],
    }
    expect(requiredPorts(node).map(portKey)).toEqual(['out', 'v:y', 'v:z'])
  })

  it('gives head plus arg ports 0..arity-1 for atoms, read from the inline sig', () => {
    const node: DiagramNode = { kind: 'atom', region: 'r0', sig: relSig([IOTA, IOTA]) }
    expect(requiredPorts(node).map(portKey)).toEqual(['hd', 'a:0', 'a:1'])
  })

  it('gives arg ports 0..arity-1 for refs, read from the inline sig (no head, no output)', () => {
    const node: DiagramNode = { kind: 'ref', region: 'r0', defId: 'R', sig: relSig([IOTA, IOTA, IOTA]) }
    expect(requiredPorts(node).map(portKey)).toEqual(['a:0', 'a:1', 'a:2'])
  })

  it('gives output plus one freeVar port per parameter for body nodes (p0..pk)', () => {
    // sig arity 1 => boundary[0] is the arg stub; two params expose p0, p1
    const content = mkDiagramWithBoundary(
      mkDiagram({
        root: 'c0',
        regions: { c0: { kind: 'sheet' } },
        wires: {
          aw: { scope: 'c0', sig: IOTA, endpoints: [] },
          pw0: { scope: 'c0', sig: IOTA, endpoints: [] },
          pw1: { scope: 'c0', sig: relSig([IOTA]), endpoints: [] },
        },
      }),
      ['aw', 'pw0', 'pw1'],
    )
    const node: DiagramNode = { kind: 'body', region: 'r0', sig: relSig([IOTA]), content }
    expect(requiredPorts(node).map(portKey)).toEqual(['out', 'v:p0', 'v:p1'])
  })
})

describe('portSig', () => {
  it('returns IOTA for every port of a term node', () => {
    const node: DiagramNode = {
      kind: 'term', region: 'r0', term: p('\\x. y x'), freePorts: ['y'],
    }
    expect(portSig(node, { kind: 'output' })).toBe(IOTA)
    expect(portSig(node, { kind: 'freeVar', name: 'y' })).toBe(IOTA)
  })

  it('throws for a freeVar port the term node does not have', () => {
    const node: DiagramNode = {
      kind: 'term', region: 'r0', term: p('\\x. y x'), freePorts: ['y'],
    }
    expect(() => portSig(node, { kind: 'freeVar', name: 'z' })).toThrowError(DiagramError)
  })

  it('returns the whole sig for an atom head and the arg sig for each arg', () => {
    const sig = relSig([relSig([IOTA]), IOTA])
    const node: DiagramNode = { kind: 'atom', region: 'r0', sig }
    expect(sigKey(portSig(node, { kind: 'head' }))).toBe('((i),i)')
    expect(sigKey(portSig(node, { kind: 'arg', index: 0 }))).toBe('(i)')
    expect(sigKey(portSig(node, { kind: 'arg', index: 1 }))).toBe('i')
  })

  it('returns the arg sig for a ref arg port (refs have no head)', () => {
    const node: DiagramNode = { kind: 'ref', region: 'r0', defId: 'R', sig: relSig([relSig([IOTA])]) }
    expect(sigKey(portSig(node, { kind: 'arg', index: 0 }))).toBe('(i)')
    expect(() => portSig(node, { kind: 'head' })).toThrowError(DiagramError)
  })

  it('returns the whole sig for a body output and the param wire sig for each freeVar', () => {
    const content = mkDiagramWithBoundary(
      mkDiagram({
        root: 'c0',
        regions: { c0: { kind: 'sheet' } },
        wires: {
          aw: { scope: 'c0', sig: IOTA, endpoints: [] },
          pw0: { scope: 'c0', sig: relSig([IOTA]), endpoints: [] },
        },
      }),
      ['aw', 'pw0'],
    )
    const node: DiagramNode = { kind: 'body', region: 'r0', sig: relSig([IOTA]), content }
    expect(sigKey(portSig(node, { kind: 'output' }))).toBe('(i)')
    expect(sigKey(portSig(node, { kind: 'freeVar', name: 'p0' }))).toBe('(i)')
  })
})

describe('mkDiagram (happy path)', () => {
  it('constructs a valid diagram: atom X(i,i) with a term node feeding an arg', () => {
    const regions: Record<string, Region> = { r0: { kind: 'sheet' } }
    const nodes: Record<string, DiagramNodeInput> = {
      n0: { kind: 'term', region: 'r0', term: p('\\x. x') },
      n1: { kind: 'atom', region: 'r0', sig: relSig([IOTA, IOTA]) },
    }
    const wires: Record<string, Wire> = {
      wh: { scope: 'r0', sig: relSig([IOTA, IOTA]), endpoints: [{ node: 'n1', port: { kind: 'head' } }] },
      w0: {
        scope: 'r0', sig: IOTA,
        endpoints: [
          { node: 'n0', port: { kind: 'output' } },
          { node: 'n1', port: { kind: 'arg', index: 0 } },
        ],
      },
      w1: { scope: 'r0', sig: IOTA, endpoints: [{ node: 'n1', port: { kind: 'arg', index: 1 } }] },
    }
    const d = mkDiagram({ root: 'r0', regions, nodes, wires })
    expect(d.root).toBe('r0')
    expect(Object.isFrozen(d)).toBe(true)
    expect(Object.isFrozen(d.nodes)).toBe(true)
    expect(d.wires['wh']?.sig && sigKey(d.wires['wh'].sig)).toBe('(i,i)')
  })

  it('accepts a depth-2 atom: Arrow-sort head wire, two order-1 arg wires, one term arg wire', () => {
    // sig ((i),(i),i): order 2. head carries the whole sig; args carry (i),(i),i.
    const atomSig = relSig([relSig([IOTA]), relSig([IOTA]), IOTA])
    const regions: Record<string, Region> = { r0: { kind: 'sheet' } }
    const nodes: Record<string, DiagramNodeInput> = {
      a: { kind: 'atom', region: 'r0', sig: atomSig },
    }
    const wires: Record<string, Wire> = {
      wh: { scope: 'r0', sig: atomSig, endpoints: [{ node: 'a', port: { kind: 'head' } }] },
      w0: { scope: 'r0', sig: relSig([IOTA]), endpoints: [{ node: 'a', port: { kind: 'arg', index: 0 } }] },
      w1: { scope: 'r0', sig: relSig([IOTA]), endpoints: [{ node: 'a', port: { kind: 'arg', index: 1 } }] },
      w2: { scope: 'r0', sig: IOTA, endpoints: [{ node: 'a', port: { kind: 'arg', index: 2 } }] },
    }
    const d = mkDiagram({ root: 'r0', regions, nodes, wires })
    expect(sigKey(d.wires['wh']!.sig)).toBe('((i),(i),i)')
  })

  it('constructs a valid diagram with a ref node (higher-sort arg)', () => {
    const refSig = relSig([relSig([IOTA])])
    const d = mkDiagram({
      root: 'r0',
      regions: { r0: { kind: 'sheet' } },
      nodes: { r: { kind: 'ref', region: 'r0', defId: 'R', sig: refSig } },
      wires: { w0: { scope: 'r0', sig: relSig([IOTA]), endpoints: [{ node: 'r', port: { kind: 'arg', index: 0 } }] } },
    })
    expect(sigKey((d.nodes['r'] as { sig: typeof refSig }).sig)).toBe('((i))')
  })

  it('constructs a valid diagram with a body node exposing a param as a freeVar port', () => {
    const content = mkDiagramWithBoundary(
      mkDiagram({
        root: 'c0',
        regions: { c0: { kind: 'sheet' } },
        wires: {
          aw: { scope: 'c0', sig: IOTA, endpoints: [] },
          pw: { scope: 'c0', sig: IOTA, endpoints: [] },
        },
      }),
      ['aw', 'pw'],
    )
    const bodySig = relSig([IOTA])
    const d = mkDiagram({
      root: 'r0',
      regions: { r0: { kind: 'sheet' } },
      nodes: { b: { kind: 'body', region: 'r0', sig: bodySig, content } },
      wires: {
        wout: { scope: 'r0', sig: bodySig, endpoints: [{ node: 'b', port: { kind: 'output' } }] },
        wp0: { scope: 'r0', sig: IOTA, endpoints: [{ node: 'b', port: { kind: 'freeVar', name: 'p0' } }] },
      },
    })
    expect(d.nodes['b']?.kind).toBe('body')
  })

  it('accepts wires with zero endpoints (bare existence)', () => {
    const d = mkDiagram({
      root: 'r0',
      regions: { r0: { kind: 'sheet' } },
      wires: { w0: { scope: 'r0', sig: IOTA, endpoints: [] } },
    })
    expect(d.wires['w0']?.endpoints).toHaveLength(0)
  })

  it('does not alias ports across node-id/port-name boundaries (separator safety)', () => {
    const regions: Record<string, Region> = { r0: { kind: 'sheet' } }
    const nodes: Record<string, DiagramNodeInput> = {
      'n0': { kind: 'term', region: 'r0', term: { kind: 'port' as const, name: 'x out' } },
      'n0 v:x': { kind: 'term', region: 'r0', term: p('\\x. x') },
    }
    const wires: Record<string, Wire> = {
      w0: { scope: 'r0', sig: IOTA, endpoints: [{ node: 'n0', port: { kind: 'output' } }] },
      w1: { scope: 'r0', sig: IOTA, endpoints: [{ node: 'n0', port: { kind: 'freeVar', name: 'x out' } }] },
      w2: { scope: 'r0', sig: IOTA, endpoints: [{ node: 'n0 v:x', port: { kind: 'output' } }] },
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
        scope: 'r0', sig: IOTA,
        endpoints: [
          { node: 'n0', port: { kind: 'output' } },
          { node: 'n1', port: { kind: 'output' } },
        ],
      },
    }
    expect(() => mkDiagram({ root: 'r0', regions, nodes, wires })).not.toThrow()
  })

  it('canonicalizes term free ports to s0, s1, … rewriting freeVar endpoints', () => {
    const d = mkDiagram({
      root: 'r0',
      regions: { r0: { kind: 'sheet' } },
      nodes: { n0: { kind: 'term', region: 'r0', term: p('y x'), freePorts: ['y', 'x'] } },
      wires: {
        wo: { scope: 'r0', sig: IOTA, endpoints: [{ node: 'n0', port: { kind: 'output' } }] },
        w0: { scope: 'r0', sig: IOTA, endpoints: [{ node: 'n0', port: { kind: 'freeVar', name: 'y' } }] },
        w1: { scope: 'r0', sig: IOTA, endpoints: [{ node: 'n0', port: { kind: 'freeVar', name: 'x' } }] },
      },
    })
    const node = d.nodes['n0'] as Extract<DiagramNode, { kind: 'term' }>
    expect(node.freePorts).toEqual(['s0', 's1'])
  })
})

describe('mkDiagram (sort checking)', () => {
  it('rejects a wire whose sig does not match the atom head port sort', () => {
    const nodes: Record<string, DiagramNodeInput> = {
      a: { kind: 'atom', region: 'r0', sig: relSig([IOTA, IOTA]) },
    }
    const wires: Record<string, Wire> = {
      wh: { scope: 'r0', sig: relSig([IOTA]), endpoints: [{ node: 'a', port: { kind: 'head' } }] },
      w0: { scope: 'r0', sig: IOTA, endpoints: [{ node: 'a', port: { kind: 'arg', index: 0 } }] },
      w1: { scope: 'r0', sig: IOTA, endpoints: [{ node: 'a', port: { kind: 'arg', index: 1 } }] },
    }
    expect(() => mkDiagram({ root: 'r0', regions: { r0: { kind: 'sheet' } }, nodes, wires }))
      .toThrowError(/wire 'wh' sig '\(i\)' does not match port 'hd' of node 'a' expecting '\(i,i\)'/)
  })

  it('rejects a plain iota wire (i) plugged into an order-1 arg port (i)', () => {
    // atom sig ((i)): its single arg port accepts an order-1 relation, not an individual.
    const atomSig = relSig([relSig([IOTA])])
    const nodes: Record<string, DiagramNodeInput> = {
      a: { kind: 'atom', region: 'r0', sig: atomSig },
    }
    const wires: Record<string, Wire> = {
      wh: { scope: 'r0', sig: atomSig, endpoints: [{ node: 'a', port: { kind: 'head' } }] },
      w0: { scope: 'r0', sig: IOTA, endpoints: [{ node: 'a', port: { kind: 'arg', index: 0 } }] },
    }
    expect(() => mkDiagram({ root: 'r0', regions: { r0: { kind: 'sheet' } }, nodes, wires }))
      .toThrowError(/wire 'w0' sig 'i' does not match port 'a:0' of node 'a' expecting '\(i\)'/)
  })

  it('rejects a wire whose sig does not match a ref arg port sort', () => {
    const nodes: Record<string, DiagramNodeInput> = {
      r: { kind: 'ref', region: 'r0', defId: 'R', sig: relSig([relSig([IOTA])]) },
    }
    const wires: Record<string, Wire> = {
      w0: { scope: 'r0', sig: IOTA, endpoints: [{ node: 'r', port: { kind: 'arg', index: 0 } }] },
    }
    expect(() => mkDiagram({ root: 'r0', regions: { r0: { kind: 'sheet' } }, nodes, wires }))
      .toThrowError(/wire 'w0' sig 'i' does not match port 'a:0' of node 'r' expecting '\(i\)'/)
  })

  it('rejects a wire whose sig does not match a body param (freeVar) port sort', () => {
    const content = mkDiagramWithBoundary(
      mkDiagram({
        root: 'c0',
        regions: { c0: { kind: 'sheet' } },
        wires: {
          aw: { scope: 'c0', sig: IOTA, endpoints: [] },
          pw: { scope: 'c0', sig: relSig([IOTA]), endpoints: [] },
        },
      }),
      ['aw', 'pw'],
    )
    const bodySig = relSig([IOTA])
    const nodes: Record<string, DiagramNodeInput> = {
      b: { kind: 'body', region: 'r0', sig: bodySig, content },
    }
    const wires: Record<string, Wire> = {
      wout: { scope: 'r0', sig: bodySig, endpoints: [{ node: 'b', port: { kind: 'output' } }] },
      // p0 param wire in content is (i); feeding a plain i here is a sort error.
      wp0: { scope: 'r0', sig: IOTA, endpoints: [{ node: 'b', port: { kind: 'freeVar', name: 'p0' } }] },
    }
    expect(() => mkDiagram({ root: 'r0', regions: { r0: { kind: 'sheet' } }, nodes, wires }))
      .toThrowError(/wire 'wp0' sig 'i' does not match port 'v:p0' of node 'b' expecting '\(i\)'/)
  })

  it('rejects a wire whose sig does not match a body output port sort', () => {
    const content = mkDiagramWithBoundary(
      mkDiagram({
        root: 'c0',
        regions: { c0: { kind: 'sheet' } },
        wires: { aw: { scope: 'c0', sig: IOTA, endpoints: [] } },
      }),
      ['aw'],
    )
    const bodySig = relSig([IOTA])
    const nodes: Record<string, DiagramNodeInput> = {
      b: { kind: 'body', region: 'r0', sig: bodySig, content },
    }
    const wires: Record<string, Wire> = {
      wout: { scope: 'r0', sig: IOTA, endpoints: [{ node: 'b', port: { kind: 'output' } }] },
    }
    expect(() => mkDiagram({ root: 'r0', regions: { r0: { kind: 'sheet' } }, nodes, wires }))
      .toThrowError(/wire 'wout' sig 'i' does not match port 'out' of node 'b' expecting '\(i\)'/)
  })
})

describe('mkDiagram (body content coherence)', () => {
  it('rejects a body node whose boundary is shorter than its sig arity', () => {
    const content = mkDiagramWithBoundary(
      mkDiagram({
        root: 'c0',
        regions: { c0: { kind: 'sheet' } },
        wires: { aw: { scope: 'c0', sig: IOTA, endpoints: [] } },
      }),
      ['aw'],
    )
    // sig arity 2 but boundary length 1
    const nodes: Record<string, DiagramNodeInput> = {
      b: { kind: 'body', region: 'r0', sig: relSig([IOTA, IOTA]), content },
    }
    expect(() => mkDiagram({ root: 'r0', regions: { r0: { kind: 'sheet' } }, nodes }))
      .toThrowError(/body node 'b' boundary length 1 is shorter than sig arity 2/)
  })

  it('rejects a body node whose arg-stub boundary sig disagrees with the sig arg', () => {
    const content = mkDiagramWithBoundary(
      mkDiagram({
        root: 'c0',
        regions: { c0: { kind: 'sheet' } },
        wires: { aw: { scope: 'c0', sig: IOTA, endpoints: [] } },
      }),
      ['aw'],
    )
    // boundary[0] is (i) in content? no — it is i; sig arg 0 declares (i): mismatch.
    const nodes: Record<string, DiagramNodeInput> = {
      b: { kind: 'body', region: 'r0', sig: relSig([relSig([IOTA])]), content },
    }
    expect(() => mkDiagram({ root: 'r0', regions: { r0: { kind: 'sheet' } }, nodes }))
      .toThrowError(/body node 'b' boundary\[0\] wire 'aw' sig 'i' does not match sig arg 0 '\(i\)'/)
  })
})

describe('mkDiagram (structural rejections)', () => {
  it('rejects a second sheet', () => {
    expect(() => mkDiagram({
      root: 'r0',
      regions: { r0: { kind: 'sheet' }, r1: { kind: 'sheet' } },
    })).toThrowError(/region 'r1' is a second sheet/)
  })

  it('rejects a region parent cycle', () => {
    expect(() => mkDiagram({
      root: 'r0',
      regions: {
        r0: { kind: 'sheet' },
        r1: { kind: 'cut', parent: 'r2' },
        r2: { kind: 'cut', parent: 'r1' },
      },
    })).toThrowError(/cycle/)
  })

  it('rejects a required port not attached to any wire', () => {
    const nodes: Record<string, DiagramNodeInput> = {
      a: { kind: 'atom', region: 'r0', sig: relSig([IOTA]) },
    }
    const wires: Record<string, Wire> = {
      wh: { scope: 'r0', sig: relSig([IOTA]), endpoints: [{ node: 'a', port: { kind: 'head' } }] },
      // arg 0 left unattached
    }
    expect(() => mkDiagram({ root: 'r0', regions: { r0: { kind: 'sheet' } }, nodes, wires }))
      .toThrowError(/port 'a:0' of node 'a' is not attached to any wire/)
  })

  it('rejects the same port attached to two wires', () => {
    const nodes: Record<string, DiagramNodeInput> = {
      a: { kind: 'atom', region: 'r0', sig: relSig([IOTA]) },
    }
    const wires: Record<string, Wire> = {
      wh: { scope: 'r0', sig: relSig([IOTA]), endpoints: [{ node: 'a', port: { kind: 'head' } }] },
      w0: { scope: 'r0', sig: IOTA, endpoints: [{ node: 'a', port: { kind: 'arg', index: 0 } }] },
      w0b: { scope: 'r0', sig: IOTA, endpoints: [{ node: 'a', port: { kind: 'arg', index: 0 } }] },
    }
    expect(() => mkDiagram({ root: 'r0', regions: { r0: { kind: 'sheet' } }, nodes, wires }))
      .toThrowError(/port 'a:0' of node 'a' is attached to two wires/)
  })

  it('rejects an endpoint referencing a non-existent port', () => {
    const nodes: Record<string, DiagramNodeInput> = {
      a: { kind: 'atom', region: 'r0', sig: relSig([IOTA]) },
    }
    const wires: Record<string, Wire> = {
      wh: { scope: 'r0', sig: relSig([IOTA]), endpoints: [{ node: 'a', port: { kind: 'head' } }] },
      w0: { scope: 'r0', sig: IOTA, endpoints: [{ node: 'a', port: { kind: 'arg', index: 0 } }] },
      wbad: { scope: 'r0', sig: IOTA, endpoints: [{ node: 'a', port: { kind: 'arg', index: 5 } }] },
    }
    expect(() => mkDiagram({ root: 'r0', regions: { r0: { kind: 'sheet' } }, nodes, wires }))
      .toThrowError(/non-existent port 'a:5' of node 'a'/)
  })

  it('rejects a malformed wire sig', () => {
    const wires = {
      w0: { scope: 'r0', sig: { kind: 'rel' } as unknown as Wire['sig'], endpoints: [] },
    }
    expect(() => mkDiagram({ root: 'r0', regions: { r0: { kind: 'sheet' } }, wires }))
      .toThrowError(/wire 'w0' sig/)
  })
})

describe('DiagramError', () => {
  it('is a distinct error class', () => {
    expect(new DiagramError('x')).toBeInstanceOf(Error)
    expect(new DiagramError('x').name).toBe('DiagramError')
  })
})
