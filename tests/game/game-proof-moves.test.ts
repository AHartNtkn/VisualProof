import { describe, expect, it } from 'vitest'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { mkDiagramWithBoundary } from '../../src/kernel/diagram/boundary'
import { EMPTY_PROOF_CONTEXT, verifyTheory } from '../../src/kernel/proof/context'
import {
  discoverGameProofActions,
  proofShortcutStep,
} from '../../src/game/interface/proof-moves'
import {
  mapProofClient,
  proofSurfaceInputAllowed,
  proofSurfaceViewportAllowed,
  routeGameProofClaim,
} from '../../src/game/interface/proof-surface'

const key = (value: Partial<{
  key: string
  shiftKey: boolean
  ctrlKey: boolean
  altKey: boolean
  metaKey: boolean
  repeat: boolean
}> = {}) => ({
  key: '', shiftKey: false, ctrlKey: false, altKey: false, metaKey: false, repeat: false, ...value,
})

describe('game proof move routing', () => {
  it('routes exactly one unmodified F shortcut for one selected wire', () => {
    expect(proofShortcutStep(key({ key: 'F' }), [{ kind: 'wire', id: 'w0' }]))
      .toEqual({ rule: 'fusion', wire: 'w0' })
    expect(proofShortcutStep(key({ key: 'f', ctrlKey: true }), [{ kind: 'wire', id: 'w0' }])).toBeNull()
    expect(proofShortcutStep(key({ key: 'F', repeat: true }), [{ kind: 'wire', id: 'w0' }])).toBeNull()
    expect(proofShortcutStep(key({ key: 'F' }), [{ kind: 'wire', id: 'w0' }, { kind: 'wire', id: 'w1' }])).toBeNull()
  })

  it('never discovers theorem citation actions even when theorem authority exists', () => {
    const builder = new DiagramBuilder()
    const cut = builder.cut(builder.root)
    const diagram = builder.build()
    const empty = new DiagramBuilder().build()
    const context = verifyTheory({ relations: [], theorems: [{
      name: 'forbidden-picker-entry',
      lhs: mkDiagramWithBoundary(empty, []),
      rhs: mkDiagramWithBoundary(empty, []),
      actions: [],
    }] })
    const discovery = discoverGameProofActions(
      diagram,
      [{ kind: 'region', id: cut }],
      context,
    )

    expect(discovery?.actions.map((action) => action.kind)).not.toContain('citeTheorem')
    expect(JSON.stringify(discovery)).not.toMatch(/theorem|citation|reference/i)
  })

  it('does not invent a selection action for empty-space spawning', () => {
    const builder = new DiagramBuilder()
    const diagram = builder.build()
    expect(discoverGameProofActions(diagram, [], EMPTY_PROOF_CONTEXT)).toBeNull()
  })

  it('gives an open loupe exclusive proof authority while retaining its constrained host viewport', () => {
    expect(proofSurfaceInputAllowed(false, false, true)).toBe(true)
    expect(proofSurfaceInputAllowed(true, false, true)).toBe(false)
    expect(proofSurfaceViewportAllowed(false, true)).toBe(true)
    expect(proofSurfaceViewportAllowed(true, true)).toBe(false)
    const claim = {
      still: 'claim' as const,
      blocksPassiveRelaxation: true,
      move: () => {}, release: () => {}, cancel: () => {},
    }
    let hostClaims = 0
    let proofClaims = 0
    const sample = {
      pointerId: 1,
      button: 0,
      client: { x: 10, y: 20 },
      screen: { x: 10, y: 20 },
      world: { x: 1, y: 2 },
      hit: { kind: 'wire' as const, id: 'host-wire' },
      shiftKey: false,
      ctrlKey: false,
      altKey: false,
      metaKey: false,
    }
    expect(routeGameProofClaim(
      { hostClaim: () => { hostClaims++; return claim } },
      { claim: () => { proofClaims++; return null } },
      sample,
    )).toBe(claim)
    expect({ hostClaims, proofClaims }).toEqual({ hostClaims: 1, proofClaims: 0 })
  })

  it('maps live client pixels through backing-store screen coordinates exactly once', () => {
    expect(mapProofClient(
      { x: 210, y: 120 },
      { left: 10, top: 20, width: 400, height: 200 },
      { width: 800, height: 400 },
      { scale: 4, offsetX: 20, offsetY: 40 },
    )).toEqual({ screen: { x: 400, y: 200 }, world: { x: 95, y: 40 } })
  })
})
