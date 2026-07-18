import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../../src/kernel/term/parse'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { mkSelection } from '../../../src/kernel/diagram/subgraph/selection'
import { exploreForm } from '../../../src/kernel/diagram/canonical/explore'
import { applyErasure } from '../../../src/kernel/rules/erasure'
import { applyConversion } from '../../../src/kernel/rules/conversion'
import { applyHeadStrip } from '../../../src/kernel/rules/headstrip'
import { applyClosedTermIntro } from '../../../src/kernel/rules/intro'
import {
  applyStep,
  applyStepWithReceipt,
  replayProof,
  transportBoundary,
} from '../../../src/kernel/proof/step'
import type { ProofContext, ProofStep } from '../../../src/kernel/proof/step'
import { ProofError } from '../../../src/kernel/proof/error'

const pp = (s: string) => parseTerm(s)

const ctx: ProofContext = { theorems: new Map(), relations: new Map() }

describe('applyStep mirrors the direct appliers', () => {
  it('erasure step equals applyErasure', () => {
    const h = new DiagramBuilder()
    const n = h.termNode(h.root, pp('\\x. x'))
    h.cut(h.root)
    const d = h.build()
    const sel = mkSelection(d, { region: d.root, regions: [], nodes: [n], wires: [] })
    const step: ProofStep = { rule: 'erasure', sel }
    expect(exploreForm(applyStep(d, step, ctx))).toBe(exploreForm(applyErasure(d, sel)))
  })

  it('conversion step replays by certificate, fuel-free', () => {
    const h = new DiagramBuilder()
    const n = h.termNode(h.root, pp('(\\x. x) y'))
    const d = h.build()
    // the node's source free 'y' is canonical s0 after construction
    const { diagram, certificate } = applyConversion(d, n, pp('s0'), 10)
    const step: ProofStep = { rule: 'conversion', node: n, term: pp('s0'), certificate, attachments: {} }
    expect(exploreForm(applyStep(d, step, ctx))).toBe(exploreForm(diagram))
  })

  it('congruenceJoin step merges the outputs of βη-equal co-resident nodes', () => {
    const h = new DiagramBuilder()
    const n1 = h.termNode(h.root, pp('y'))
    const n2 = h.termNode(h.root, pp('y'))
    h.wire(h.root, [
      { node: n1, port: { kind: 'freeVar', name: 'y' } },
      { node: n2, port: { kind: 'freeVar', name: 'y' } },
    ])
    h.wire(h.root, [{ node: n1, port: { kind: 'output' } }])
    h.wire(h.root, [{ node: n2, port: { kind: 'output' } }])
    const d = h.build()
    const step: ProofStep = { rule: 'congruenceJoin', a: n1, b: n2, certificate: { leftSteps: [], rightSteps: [] } }
    const out = applyStep(d, step, ctx)
    const shared = Object.values(out.wires).find((w) => w.endpoints.filter((ep) => ep.port.kind === 'output').length === 2)
    expect(shared).toBeDefined()
  })

  it('closedTermIntro step mints a closed term node, replaying through replayProof', () => {
    const h = new DiagramBuilder()
    const cut = h.cut(h.root)
    const d = h.build()
    const step: ProofStep = { rule: 'closedTermIntro', region: cut, term: pp('\\x. \\y. x') }
    expect(exploreForm(applyStep(d, step, ctx)))
      .toBe(exploreForm(applyClosedTermIntro(d, cut, pp('\\x. \\y. x'))))
    const out = replayProof(d, [step], ctx)
    const added = Object.entries(out.nodes).filter(([id]) => d.nodes[id] === undefined)
    expect(added).toHaveLength(1)
    expect(added[0]![1].region).toBe(cut)
  })

  it('headStrip step decomposes a rigid-head equation, replaying through replayProof', () => {
    const h = new DiagramBuilder()
    const n1 = h.termNode(h.root, pp('\\x. x a b'))
    const n2 = h.termNode(h.root, pp('\\x. x a c'))
    h.wire(h.root, [
      { node: n1, port: { kind: 'freeVar', name: 'a' } },
      { node: n2, port: { kind: 'freeVar', name: 'a' } },
    ])
    h.wire(h.root, [
      { node: n1, port: { kind: 'output' } },
      { node: n2, port: { kind: 'output' } },
    ])
    const d = h.build()
    const step: ProofStep = { rule: 'headStrip', a: n1, b: n2 }
    expect(exploreForm(applyStep(d, step, ctx))).toBe(exploreForm(applyHeadStrip(d, n1, n2)))
    const out = replayProof(d, [step], ctx)
    expect(Object.keys(out.nodes)).toHaveLength(4)
  })

  it('double-cut intro/elim and iteration/deiteration round-trip through steps', () => {
    const h = new DiagramBuilder()
    const n = h.termNode(h.root, pp('y'))
    const hub = h.termNode(h.root, pp('\\x. x'))
    h.wire(h.root, [
      { node: n, port: { kind: 'freeVar', name: 'y' } },
      { node: hub, port: { kind: 'output' } },
    ])
    const cut = h.cut(h.root)
    const d = h.build()
    const sel = mkSelection(d, { region: d.root, regions: [], nodes: [n], wires: [] })
    const steps: ProofStep[] = [
      { rule: 'iteration', sel, target: cut },
      { rule: 'doubleCutIntro', sel },
    ]
    const out = replayProof(d, steps, ctx)
    expect(Object.keys(out.regions).length).toBe(Object.keys(d.regions).length + 2)
  })

  it('atomic open-term spawning replays through the proof dispatcher', () => {
    const h = new DiagramBuilder()
    const cut = h.cut(h.root)
    const d = h.build()
    const out = applyStep(d, { rule: 'openTermSpawn', region: cut, term: pp('x') }, ctx)
    expect(Object.values(out.nodes)).toHaveLength(1)
  })
})

describe('step interface transport', () => {
  const anchoredFixture = (survivorBehindCut: boolean) => {
    const b = new DiagramBuilder()
    const cut = b.cut(b.root)
    const redundant = b.termNode(b.root, pp('\\x. x'))
    const survivor = b.termNode(survivorBehindCut ? cut : b.root, pp('\\x. x'))
    const drop = b.wire(b.root, [{ node: redundant, port: { kind: 'output' } }])
    const keep = b.wire(b.root, [{ node: survivor, port: { kind: 'output' } }])
    return { diagram: b.build(), redundant, survivor, drop, keep }
  }

  it('coalesces an anchored contraction boundary exactly when the survivor is root-available', () => {
    const root = anchoredFixture(false)
    const rootReceipt = applyStepWithReceipt(root.diagram, {
      rule: 'anchoredWireContract',
      redundant: root.redundant,
      survivor: root.survivor,
      certificate: { leftSteps: [], rightSteps: [] },
    }, ctx)
    expect(rootReceipt.result.wires[root.drop]).toBeUndefined()
    expect(rootReceipt.interface.image(root.drop)).toBe(root.keep)
    expect(transportBoundary(rootReceipt.interface, [root.drop, root.drop, root.keep]))
      .toEqual([root.keep, root.keep, root.keep])

    const shielded = anchoredFixture(true)
    const shieldedReceipt = applyStepWithReceipt(shielded.diagram, {
      rule: 'anchoredWireContract',
      redundant: shielded.redundant,
      survivor: shielded.survivor,
      certificate: { leftSteps: [], rightSteps: [] },
    }, ctx)
    expect(shieldedReceipt.result.wires[shielded.drop]).toBeUndefined()
    expect(shieldedReceipt.interface.image(shielded.drop)).toBeUndefined()
    expect(transportBoundary(shieldedReceipt.interface, [shielded.drop])).toBeUndefined()
    expect(transportBoundary(shieldedReceipt.interface, [shielded.keep])).toEqual([shielded.keep])
  })

  it('uses the same coalescing interface authority for wire join', () => {
    const b = new DiagramBuilder()
    const outerNode = b.termNode(b.root, pp('\\x. x'))
    const innerNode = b.termNode(b.root, pp('\\x. x'))
    const outer = b.wire(b.root, [{ node: outerNode, port: { kind: 'output' } }])
    const inner = b.wire(b.root, [{ node: innerNode, port: { kind: 'output' } }])
    const receipt = applyStepWithReceipt(
      b.build(),
      { rule: 'wireJoin', a: outer, b: inner },
      ctx,
      'backward',
    )
    expect(transportBoundary(receipt.interface, [outer, inner, inner]))
      .toEqual([outer, outer, outer])
  })
})

describe('replayProof failure reporting', () => {
  it('names the failing step index and rule', () => {
    const h = new DiagramBuilder()
    const cut = h.cut(h.root)
    const n = h.termNode(cut, pp('\\x. x'))
    const d = h.build()
    const sel = mkSelection(d, { region: cut, regions: [], nodes: [n], wires: [] })
    let caught: unknown
    try {
      replayProof(d, [{ rule: 'erasure', sel }], ctx) // negative region: gate refuses
    } catch (e) { caught = e }
    expect(caught).toBeInstanceOf(ProofError)
    expect((caught as Error).message).toMatch(/step 0 \(erasure\) failed: erasure requires a positive region/)
  })

  it('unknown theorem names fail loudly', () => {
    const d = new DiagramBuilder().build()
    expect(() => applyStep(d, {
      rule: 'theorem', name: 'ghost',
      at: { sel: { region: d.root, regions: [], nodes: [], wires: [] }, args: [] },
      direction: 'forward',
    }, ctx)).toThrowError(/unknown theorem 'ghost'/)
  })
})
