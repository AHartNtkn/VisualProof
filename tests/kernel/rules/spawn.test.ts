import { describe, expect, it } from 'vitest'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { mkDiagramWithBoundary } from '../../../src/kernel/diagram/boundary'
import { relSig, TERM } from '../../../src/kernel/diagram/sig'
import { parseTerm } from '../../../src/kernel/term/parse'
import {
  applyBoundRelationSpawn,
  applyOpenTermSpawn,
  applyRelationSpawn,
} from '../../../src/kernel/rules/spawn'

const p = (source: string) => parseTerm(source)
const arity2 = relSig([TERM, TERM])

function host() {
  const builder = new DiagramBuilder()
  const cut = builder.cut(builder.root)
  // A sibling cut, at the same depth as `cut` but outside `relWire`'s scope —
  // exercises the "does not enclose" gate below.
  const siblingCut = builder.cut(builder.root)
  const relWire = builder.relWire(cut, arity2)
  const innerCut = builder.cut(cut)
  return { diagram: builder.build(), root: builder.root, cut, siblingCut, relWire, innerCut }
}

function relations() {
  const body = new DiagramBuilder()
  const left = body.wire(body.root, [])
  const right = body.wire(body.root, [])
  return new Map([['logic/R', mkDiagramWithBoundary(body.build(), [left, right])]])
}

/** Wires created by a spawn: `relWire` in `host()` pre-exists (endpoint-free,
 *  the bound-relation identity), so filter it out to isolate the fresh set. */
function freshWires(before: ReturnType<typeof host>['diagram'], after: ReturnType<typeof host>['diagram']) {
  return Object.entries(after.wires).filter(([id]) => before.wires[id] === undefined).map(([, w]) => w)
}

describe('atomic proof spawning', () => {
  it('spawns one open term with one singleton wire per required port', () => {
    const h = host()
    const out = applyOpenTermSpawn(h.diagram, h.cut, p('f x'), ['f', 'x'], 'forward')
    expect(Object.keys(out.nodes)).toHaveLength(1)
    const fresh = freshWires(h.diagram, out)
    expect(fresh).toHaveLength(3)
    expect(fresh.every((wire) => wire.scope === h.cut && wire.endpoints.length === 1)).toBe(true)
  })

  it('accepts a closed term with one explicit unused port', () => {
    const h = host()
    const out = applyOpenTermSpawn(h.diagram, h.cut, p('\\x. x'), ['unused'], 'forward')
    const node = Object.values(out.nodes)[0]
    expect(node?.kind === 'term' && node.freePorts).toEqual(['s0'])
    expect(freshWires(h.diagram, out).map((wire) => wire.endpoints[0]?.port)).toEqual([
      { kind: 'output' },
      { kind: 'freeVar', name: 's0' },
    ])
  })

  it('preserves declared order independently of syntactic support order', () => {
    const h = host()
    const out = applyOpenTermSpawn(h.diagram, h.cut, p('used'), ['unused', 'used'], 'forward')
    const node = Object.values(out.nodes)[0]
    expect(node?.kind === 'term' && node.freePorts).toEqual(['s0', 's1'])
    expect(node?.kind === 'term' && node.term).toEqual({ kind: 'port', name: 's1' })
    expect(freshWires(h.diagram, out).map((wire) => wire.endpoints[0]?.port)).toEqual([
      { kind: 'output' },
      { kind: 'freeVar', name: 's0' },
      { kind: 'freeVar', name: 's1' },
    ])
  })

  it('requires a nonempty, unique declared interface covering syntactic support', () => {
    const h = host()
    expect(() => applyOpenTermSpawn(h.diagram, h.cut, p('x'), [], 'forward'))
      .toThrow(/at least one declared free port/)
    expect(() => applyOpenTermSpawn(h.diagram, h.cut, p('x'), ['x', 'x'], 'forward'))
      .toThrow(/unique|repeated/)
    expect(() => applyOpenTermSpawn(h.diagram, h.cut, p('x'), ['unused'], 'forward'))
      .toThrow(/does not declare|cover.*x/)
    expect(() => applyOpenTermSpawn(h.diagram, h.cut, p('x'), [''], 'forward'))
      .toThrow(/nonempty/)
  })

  it('revalidates named relation identity and arity before spawning', () => {
    const h = host()
    const context = relations()
    const out = applyRelationSpawn(h.diagram, h.cut, 'logic/R', arity2, context, 'forward')
    expect(Object.values(out.nodes)).toEqual([
      expect.objectContaining({ kind: 'ref', region: h.cut, defId: 'logic/R', sig: arity2 }),
    ])
    expect(() => applyRelationSpawn(h.diagram, h.cut, 'logic/R', relSig([TERM]), context, 'forward')).toThrow(/changed.*arity|arity.*changed/)
    expect(() => applyRelationSpawn(h.diagram, h.cut, 'missing', arity2, context, 'forward')).toThrow(/no longer loaded/)
  })

  it('shares one flipped polarity gate and additionally validates bound-relation scope', () => {
    const h = host()
    expect(() => applyOpenTermSpawn(h.diagram, h.root, p('x'), ['x'], 'forward')).toThrow(/negative region/)
    expect(() => applyOpenTermSpawn(h.diagram, h.root, p('x'), ['x'], 'backward')).not.toThrow()
    expect(() => applyRelationSpawn(h.diagram, h.root, 'logic/R', arity2, relations(), 'forward')).toThrow(/negative region/)
    expect(() => applyRelationSpawn(h.diagram, h.root, 'logic/R', arity2, relations(), 'backward')).not.toThrow()

    const out = applyBoundRelationSpawn(h.diagram, h.cut, h.relWire, 'forward')
    expect(Object.values(out.nodes)).toEqual([
      expect.objectContaining({ kind: 'atom', region: h.cut, sig: arity2 }),
    ])
    // The wire's scope must enclose the spawn region — a sibling cut outside
    // relWire's scope is refused (mkDiagram's own scope-encloses-node check,
    // the successor of the old explicit binder-ancestry gate).
    expect(() => applyBoundRelationSpawn(h.diagram, h.siblingCut, h.relWire, 'forward')).toThrow(/does not enclose/)
    expect(() => applyBoundRelationSpawn(h.diagram, h.innerCut, h.relWire, 'backward')).not.toThrow()
  })
})
