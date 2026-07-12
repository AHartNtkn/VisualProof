import { describe, expect, it } from 'vitest'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { mkDiagramWithBoundary } from '../../../src/kernel/diagram/boundary'
import { parseTerm } from '../../../src/kernel/term/parse'
import {
  applyBoundRelationSpawn,
  applyOpenTermSpawn,
  applyRelationSpawn,
} from '../../../src/kernel/rules/spawn'

const p = (source: string) => parseTerm(source)

function host() {
  const builder = new DiagramBuilder()
  const cut = builder.cut(builder.root)
  const bubble = builder.bubble(cut, 2)
  const innerCut = builder.cut(bubble)
  return { diagram: builder.build(), root: builder.root, cut, bubble, innerCut }
}

function relations() {
  const body = new DiagramBuilder()
  const left = body.wire(body.root, [])
  const right = body.wire(body.root, [])
  return new Map([['logic/R', mkDiagramWithBoundary(body.build(), [left, right])]])
}

describe('atomic proof spawning', () => {
  it('spawns one open term with one singleton wire per required port', () => {
    const h = host()
    const out = applyOpenTermSpawn(h.diagram, h.cut, p('f x'), 'forward')
    expect(Object.keys(out.nodes)).toHaveLength(1)
    expect(Object.values(out.wires)).toHaveLength(3)
    expect(Object.values(out.wires).every((wire) => wire.scope === h.cut && wire.endpoints.length === 1)).toBe(true)
  })

  it('keeps closed terms exclusively under closed-term introduction', () => {
    const h = host()
    expect(() => applyOpenTermSpawn(h.diagram, h.cut, p('\\x. x'), 'forward'))
      .toThrow(/requires at least one free port.*closed-term introduction/)
  })

  it('revalidates named relation identity and arity before spawning', () => {
    const h = host()
    const context = relations()
    const out = applyRelationSpawn(h.diagram, h.cut, 'logic/R', 2, context, 'forward')
    expect(Object.values(out.nodes)).toEqual([
      expect.objectContaining({ kind: 'ref', region: h.cut, defId: 'logic/R', arity: 2 }),
    ])
    expect(() => applyRelationSpawn(h.diagram, h.cut, 'logic/R', 1, context, 'forward')).toThrow(/changed.*arity|arity.*changed/)
    expect(() => applyRelationSpawn(h.diagram, h.cut, 'missing', 2, context, 'forward')).toThrow(/no longer loaded/)
  })

  it('shares one flipped polarity gate and additionally validates bound-relation scope', () => {
    const h = host()
    expect(() => applyOpenTermSpawn(h.diagram, h.root, p('x'), 'forward')).toThrow(/negative region/)
    expect(() => applyOpenTermSpawn(h.diagram, h.root, p('x'), 'backward')).not.toThrow()
    expect(() => applyRelationSpawn(h.diagram, h.root, 'logic/R', 2, relations(), 'forward')).toThrow(/negative region/)
    expect(() => applyRelationSpawn(h.diagram, h.root, 'logic/R', 2, relations(), 'backward')).not.toThrow()

    const out = applyBoundRelationSpawn(h.diagram, h.bubble, h.bubble, 'forward')
    expect(Object.values(out.nodes)).toEqual([
      expect.objectContaining({ kind: 'atom', region: h.bubble, binder: h.bubble }),
    ])
    expect(() => applyBoundRelationSpawn(h.diagram, h.cut, h.bubble, 'forward')).toThrow(/does not enclose/)
    expect(() => applyBoundRelationSpawn(h.diagram, h.innerCut, h.bubble, 'backward')).not.toThrow()
  })
})
