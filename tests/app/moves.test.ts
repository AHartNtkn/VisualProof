import { describe, expect, it } from 'vitest'
import { applicableActions } from '../../src/app/actions'
import { preparedMembrane } from '../../src/app/hittest'
import {
  ProofMoveController,
  proofConnectionStep,
} from '../../src/app/interact/moves'
import type { PointerSample } from '../../src/app/interact/viewport'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { IOTA, relSig } from '../../src/kernel/diagram/sig'
import { mkSelection } from '../../src/kernel/diagram/subgraph/selection'
import { EMPTY_PROOF_CONTEXT } from '../../src/kernel/proof/context'
import { applyDoubleCutIntro } from '../../src/kernel/rules/doublecut'
import { mkEngine } from '../../src/view/engine'
import { LIGHT } from '../../src/view/paint'
import { vec } from '../../src/view/vec'
import { UNARY } from '../fixtures/zero-signature'

describe('proof move vocabulary', () => {
  it('discovers only structural descriptors', () => {
    const builder = new DiagramBuilder()
    const node = builder.ref(builder.root, 'Unknown', UNARY)
    const diagram = builder.build()
    const selection = mkSelection(diagram, {
      region: diagram.root, regions: [], nodes: [node], wires: [],
    })
    const kinds = applicableActions(diagram, selection, EMPTY_PROOF_CONTEXT)
      .map((action) => action.kind)
    expect(kinds).toContain('erase')
    expect(kinds).toContain('iterate')
    expect(kinds).not.toContain('convert')
    expect(kinds).not.toContain('instantiate')
    expect(kinds).not.toContain('abstract')
    expect(kinds).not.toContain('relationJoin')
    expect(kinds).not.toContain('relationSever')
  })

  it('constructs direct connection drags only as durable IOTA joins', () => {
    const builder = new DiagramBuilder()
    const negative = builder.cut(builder.root)
    const left = builder.wire(negative, [], IOTA)
    const right = builder.wire(negative, [], IOTA)
    const diagram = builder.build()

    expect(proofConnectionStep(
      diagram,
      { wire: left, endpoint: null },
      { wire: right, endpoint: null },
      'forward',
      0,
    )).toEqual({
      rule: 'wireJoin',
      input: { kind: 'iota', a: left, b: right },
    })
  })

  it('rejects direct relation-wire merges through the kernel IOTA gate', () => {
    const builder = new DiagramBuilder()
    const negative = builder.cut(builder.root)
    const left = builder.wire(negative, [], relSig([]))
    const right = builder.wire(negative, [], relSig([]))
    const diagram = builder.build()

    expect(() => proofConnectionStep(
      diagram,
      { wire: left, endpoint: null },
      { wire: right, endpoint: null },
      'forward',
      0,
    )).toThrowError(/iota wire join requires IOTA wire/)
  })

  it('handles Escape when it aborts a pending relation wire', () => {
    const builder = new DiagramBuilder()
    const content = builder.ref(builder.root, 'NullaryBody', relSig([]))
    const diagram = builder.build()
    const wrapped = applyDoubleCutIntro(diagram, mkSelection(diagram, {
      region: diagram.root,
      regions: [],
      nodes: [content],
      wires: [],
    }))
    const inner = wrapped.nodes[content]!.region
    const outer = wrapped.regions[inner]!.kind === 'cut'
      ? wrapped.regions[inner]!.parent
      : ''
    const membrane = preparedMembrane(wrapped, outer)!
    const engine = mkEngine(wrapped, [])
    engine.bodies.get(content)!.pos = vec(0, 0)
    engine.regions.set(membrane.inner, {
      center: vec(0, 0), radius: 18, support: [],
    })
    engine.regions.set(membrane.outer, {
      center: vec(0, 0), radius: 30, support: [],
    })
    const point = vec(0, -30)
    const pointer: PointerSample = {
      pointerId: 1,
      button: 0,
      client: point,
      screen: point,
      world: point,
      hit: null,
      shiftKey: false,
      ctrlKey: false,
      altKey: false,
      metaKey: false,
    }
    const moves = new ProofMoveController({
      host: { ownerDocument: {} } as unknown as HTMLElement,
      active: () => true,
      diagram: () => wrapped,
      engine: () => engine,
      viewScale: () => 1,
      selection: () => [],
      setSelection: () => undefined,
      context: () => EMPTY_PROOF_CONTEXT,
      orientation: () => 'forward',
      apply: () => undefined,
      refuse: () => undefined,
      theme: () => LIGHT,
      fuel: () => 0,
      openSpawn: () => undefined,
    })
    const claim = moves.claim(pointer)!
    claim.release(pointer, false)
    const escape = {
      key: 'Escape',
      shiftKey: false,
      ctrlKey: false,
      altKey: false,
      metaKey: false,
      repeat: false,
    }
    expect(moves.keyDown(escape)).toBe(true)
    expect(moves.keyDown(escape)).toBe(false)
  })

})
