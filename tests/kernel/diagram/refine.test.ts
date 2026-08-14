import { describe, expect, it } from 'vitest'
import { mkDiagram, validateRawDiagram } from '../../../src/kernel/diagram/diagram'
import { refineJointly } from '../../../src/kernel/diagram/canonical/refine'
import { IOTA, relSig } from '../../../src/kernel/diagram/sig'

const rel1 = relSig([IOTA])

/** P(x) with a root pin holding the head wire. Ids parameterized. */
function atomGraph(ids: { atom: string; pin: string; head: string; value: string; valuePin: string }) {
  return mkDiagram({
    root: 'root',
    regions: { root: { kind: 'sheet' } },
    nodes: {
      [ids.atom]: { kind: 'atom', region: 'root', sig: rel1 },
      [ids.pin]: { kind: 'identity', region: 'root', sig: rel1, arity: 1 },
      [ids.valuePin]: { kind: 'identity', region: 'root', sig: IOTA, arity: 1 },
    },
    wires: {
      [ids.head]: {
        sig: rel1,
        endpoints: [
          { node: ids.atom, port: { kind: 'head' } },
          { node: ids.pin, port: { kind: 'identity', index: 0 } },
        ],
      },
      [ids.value]: {
        sig: IOTA,
        endpoints: [
          { node: ids.atom, port: { kind: 'arg', index: 0 } },
          { node: ids.valuePin, port: { kind: 'identity', index: 0 } },
        ],
      },
    },
  })
}

describe('joint refinement', () => {
  it('gives corresponding elements of isomorphic diagrams equal colors', () => {
    const a = atomGraph({ atom: 'a', pin: 'p', head: 'h', value: 'v', valuePin: 'q' })
    const b = atomGraph({ atom: 'x', pin: 'y', head: 'z', value: 'w', valuePin: 'u' })
    const [ca, cb] = refineJointly([
      { diagram: a, pins: [] },
      { diagram: b, pins: [] },
    ])
    expect(ca!.node.get('a')).toBe(cb!.node.get('x'))
    expect(ca!.node.get('p')).toBe(cb!.node.get('y'))
    expect(ca!.wire.get('h')).toBe(cb!.wire.get('z'))
    expect(ca!.wire.get('v')).toBe(cb!.wire.get('w'))
    // Distinct content gets distinct colors.
    expect(ca!.node.get('a')).not.toBe(ca!.node.get('p'))
    expect(ca!.wire.get('h')).not.toBe(ca!.wire.get('v'))
  })

  it('refines by neighborhood: two pins differing only via their wires split', () => {
    const a = atomGraph({ atom: 'a', pin: 'p', head: 'h', value: 'v', valuePin: 'q' })
    const [ca] = refineJointly([{ diagram: a, pins: [] }])
    // Both are identity nodes, but one holds a rel1 wire, the other an iota wire.
    expect(ca!.node.get('p')).not.toBe(ca!.node.get('q'))
  })

  it('marks individualize: a marked element leaves its class', () => {
    // Two interchangeable pins on one arity-2 identity's wires.
    const d = mkDiagram({
      root: 'root',
      regions: { root: { kind: 'sheet' } },
      nodes: {
        j: { kind: 'identity', region: 'root', sig: IOTA, arity: 2 },
        p0: { kind: 'identity', region: 'root', sig: IOTA, arity: 1 },
        p1: { kind: 'identity', region: 'root', sig: IOTA, arity: 1 },
      },
      wires: {
        w0: { sig: IOTA, endpoints: [
          { node: 'j', port: { kind: 'identity', index: 0 } },
          { node: 'p0', port: { kind: 'identity', index: 0 } },
        ] },
        w1: { sig: IOTA, endpoints: [
          { node: 'j', port: { kind: 'identity', index: 1 } },
          { node: 'p1', port: { kind: 'identity', index: 0 } },
        ] },
      },
    })
    const [plain] = refineJointly([{ diagram: d, pins: [] }])
    expect(plain!.wire.get('w0')).toBe(plain!.wire.get('w1'))
    const [marked] = refineJointly(
      [{ diagram: d, pins: [] }],
      [{ side: 0, sort: 'wire', id: 'w0', token: 0 }],
    )
    expect(marked!.wire.get('w0')).not.toBe(marked!.wire.get('w1'))
    // The split propagates to the pins.
    expect(marked!.node.get('p0')).not.toBe(marked!.node.get('p1'))
  })

  it('pins enter initial colors positionally', () => {
    // w0 and w1 are boundary wires (one stored end each, exposed at root):
    // with no pins they are symmetric; the ordered pin list is what splits
    // them by position.
    const d = validateRawDiagram({
      root: 'root',
      regions: { root: { kind: 'sheet' } },
      nodes: {
        j: { kind: 'identity', region: 'root', sig: IOTA, arity: 2 },
      },
      wires: {
        w0: { sig: IOTA, endpoints: [{ node: 'j', port: { kind: 'identity', index: 0 } }] },
        w1: { sig: IOTA, endpoints: [{ node: 'j', port: { kind: 'identity', index: 1 } }] },
      },
    }, ['w0', 'w1'])
    const [c] = refineJointly([{ diagram: d, pins: ['w0', 'w1'] }])
    expect(c!.wire.get('w0')).not.toBe(c!.wire.get('w1'))
  })

  it('throws on an unknown pinned wire', () => {
    const a = atomGraph({ atom: 'a', pin: 'p', head: 'h', value: 'v', valuePin: 'q' })
    expect(() => refineJointly([{ diagram: a, pins: ['nope'] }])).toThrow(/nope/)
  })
})
