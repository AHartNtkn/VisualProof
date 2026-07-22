import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../../src/kernel/term/parse'
import { mkDiagram, DiagramError, type Region, type DiagramNode, type Wire } from '../../../src/kernel/diagram/diagram'
import { relSig, TERM } from '../../../src/kernel/diagram/sig'
import { mkDiagramWithBoundary } from '../../../src/kernel/diagram/boundary'

const p = (s: string) => parseTerm(s)

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

  it('rejects an atom whose inline signature is not a relation signature', () => {
    // Successor of the old "bubble arity bounds" concern: the malformed inline
    // structural datum on a relation node is now its signature, not an arity.
    expect(() => mkDiagram({
      root: 'r0', regions: sheet,
      // TERM where a RelSig is required (typed as any to bypass the compile guard,
      // exercising the runtime constructor gate against structural literals)
      nodes: { n0: { kind: 'atom', region: 'r0', sig: TERM as never } },
    })).toThrowError(/atom node 'n0' sig must be a relation signature/)
    expect(() => mkDiagram({
      root: 'r0', regions: sheet,
      nodes: { n0: { kind: 'atom', region: 'r0', sig: { kind: 'rel', args: [{ kind: 'bogus' }] } as never } },
    })).toThrowError(/atom node 'n0' sig:.*"kind" must be "term" or "rel"/)
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

  it('rejects a body node whose content is incoherent with its signature', () => {
    // Successor of the old atom-binder placement concern: a relation node's
    // structural coherence is now enforced between its sig and its content
    // (arg-stub count and per-stub sorts), not against an enclosing bubble.
    const okContent = () => {
      const inner: Record<string, DiagramNode> = { m0: { kind: 'term', region: 'c0', term: p('\\z. z'), freePorts: [] } }
      return mkDiagram({
        root: 'c0', regions: { c0: { kind: 'sheet' } }, nodes: inner,
        wires: { cw0: { scope: 'c0', sig: TERM, endpoints: [{ node: 'm0', port: { kind: 'output' } }] } },
      })
    }
    // sig arity 1 but content exposes zero boundary wires
    expect(() => mkDiagram({
      root: 'r0', regions: sheet,
      nodes: { n0: { kind: 'body', region: 'r0', sig: relSig([TERM]),
        content: mkDiagramWithBoundary(okContent(), []) } },
    })).toThrowError(/body node 'n0' boundary length 0 is shorter than sig arity 1/)
    // sig arg sort disagrees with the arg-stub sort (rel vs term)
    expect(() => mkDiagram({
      root: 'r0', regions: sheet,
      nodes: { n0: { kind: 'body', region: 'r0', sig: relSig([relSig([TERM])]),
        content: mkDiagramWithBoundary(okContent(), ['cw0']) } },
    })).toThrowError(/body node 'n0' boundary\[0\].*does not match sig arg 0/)
  })

  const oneNode = (wires: Record<string, Wire>) => {
    const nodes: Record<string, DiagramNode> = {
      n0: { kind: 'term', region: 'r0', term: p('\\x. x'), freePorts: [] },
    }
    return mkDiagram({ root: 'r0', regions: sheet, nodes, wires })
  }

  it('rejects a wire with a missing scope', () => {
    expect(() => oneNode({ w0: { scope: 'ghost', sig: TERM, endpoints: [{ node: 'n0', port: { kind: 'output' } }] } }))
      .toThrowError(/missing scope region 'ghost'/)
  })

  it('rejects an endpoint on a missing node', () => {
    expect(() => oneNode({ w0: { scope: 'r0', sig: TERM, endpoints: [{ node: 'ghost', port: { kind: 'output' } }] } }))
      .toThrowError(/missing node 'ghost'/)
  })

  it('rejects an endpoint on a non-existent port', () => {
    expect(() => oneNode({
      w0: { scope: 'r0', sig: TERM, endpoints: [{ node: 'n0', port: { kind: 'freeVar', name: 'zz' } }] },
    })).toThrowError(/non-existent port 'v:zz'/)
  })

  it('rejects a port attached to two wires', () => {
    expect(() => oneNode({
      w0: { scope: 'r0', sig: TERM, endpoints: [{ node: 'n0', port: { kind: 'output' } }] },
      w1: { scope: 'r0', sig: TERM, endpoints: [{ node: 'n0', port: { kind: 'output' } }] },
    })).toThrowError(/attached to two wires/)
  })

  it('rejects a duplicate endpoint within a single wire, naming the wire once', () => {
    expect(() => oneNode({
      w0: {
        scope: 'r0',
        sig: TERM,
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
      wires: { w0: { scope: 'r1', sig: TERM, endpoints: [{ node: 'n0', port: { kind: 'output' } }] } },
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

  it('rejects term nodes carrying malformed terms (structural literals bypassing constructors)', () => {
    expect(() => mkDiagram({
      root: 'r0', regions: sheet,
      nodes: { n0: { kind: 'term', region: 'r0', term: { kind: 'bvar', index: 0 } } },
      wires: { w0: { scope: 'r0', sig: TERM, endpoints: [{ node: 'n0', port: { kind: 'output' } }] } },
    })).toThrowError(/node 'n0' term:.*unbound de Bruijn index/)
    expect(() => mkDiagram({
      root: 'r0', regions: sheet,
      nodes: { n0: { kind: 'term', region: 'r0', term: { kind: 'port', name: '' } } },
      wires: { w0: { scope: 'r0', sig: TERM, endpoints: [{ node: 'n0', port: { kind: 'output' } }] } },
    })).toThrowError(/node 'n0' term:.*non-empty/)
  })
})
