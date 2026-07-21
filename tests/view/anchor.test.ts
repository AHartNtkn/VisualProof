import { describe, it, expect } from 'vitest'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { mkEngine } from '../../src/view/engine'
import { settle } from '../../src/view/relax'
import { paint, LIGHT } from '../../src/view/paint'
import { hitTest, dragTarget } from '../../src/interaction/hittest'

/**
 * An empty leaf region carries an invisible ANCHOR body (its positional state
 * carrier for the relaxation). The USER LAW and the render model require it to
 * be invisible AND unselectable: it is not a kernel entity, so it must never be
 * painted (no disc, no label — that would be a satellite), never returned by a
 * hit-test (an empty cut is selected by its region circle), and never grabbed
 * directly by a drag (it moves only as its region's subtree). These pins guard
 * every one of those holes.
 */
describe('anchor bodies are invisible and unselectable', () => {
  const emptyCut = () => {
    const h = new DiagramBuilder()
    const cut = h.cut(h.root) // an empty cut — nothing inside it
    const e = mkEngine(h.build(), [])
    settle(e, 400)
    const anchor = [...e.bodies.values()].find((b) => b.kind === 'anchor')
    return { e, cut, anchor }
  }

  it('an empty cut gets exactly one anchor body, and it is the cut region’s sole member', () => {
    const { e, cut, anchor } = emptyCut()
    expect(anchor, 'empty leaf region must carry an anchor body').toBeDefined()
    expect(anchor!.region).toBe(cut)
    expect(e.membersOf.get(cut)).toEqual([anchor!.id])
    const anchors = [...e.bodies.values()].filter((b) => b.kind === 'anchor')
    expect(anchors).toHaveLength(1)
  })

  it('paint emits no disc and no label anywhere (the anchor is never drawn)', () => {
    const { e } = emptyCut()
    const shapes = paint(e, LIGHT)
    // no ref nodes exist, so the ONLY way a disc/label could appear is a
    // satellite attached to the anchor — there must be none
    expect(shapes.filter((s) => s.kind === 'label')).toHaveLength(0)
    expect(shapes.filter((s) => s.kind === 'circle' && s.fill === LIGHT.discFill)).toHaveLength(0)
  })

  it('a hit-test on the anchor position resolves to its region, never to a node', () => {
    const { e, cut, anchor } = emptyCut()
    const hit = hitTest(e, anchor!.pos, { scale: 1 })
    expect(hit).toEqual({ kind: 'region', id: cut })
  })

  it('a drag on the anchor position grabs the region subtree, never the anchor directly', () => {
    const { e, cut, anchor } = emptyCut()
    const t = dragTarget(e, anchor!.pos, { scale: 1 })
    expect(t).toEqual({ kind: 'region', id: cut })
  })
})
