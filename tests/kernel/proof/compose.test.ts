import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../../src/kernel/term/parse'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { mkDiagramWithBoundary } from '../../../src/kernel/diagram/boundary'
import { mkSelection } from '../../../src/kernel/diagram/subgraph/selection'
import { exploreForm } from '../../../src/kernel/diagram/canonical/explore'
import { replayActions } from '../../../src/kernel/proof/action'
import type { ProofAction } from '../../../src/kernel/proof/action'
import type { ProofContext, ProofStep } from '../../../src/kernel/proof/step'
import { composeActions, mapStepIds } from '../../../src/kernel/proof/compose'
import type { DiagramIso } from '../../../src/kernel/diagram/canonical/explore'

const p = (s: string) => parseTerm(s)
const ctx: ProofContext = { theorems: new Map(), relations: new Map() }
const action = (label: string, steps: readonly ProofStep[], placements: ProofAction['placements'] = []): ProofAction => ({
  label, steps, placements,
})

/** Two independently built, differently-id'd copies of the same diagram. */
function twoCopies() {
  const a = new DiagramBuilder()
  const an = a.termNode(a.root, p('y'))
  const ahub = a.termNode(a.root, p('\\x. x'))
  a.wire(a.root, [
    { node: an, port: { kind: 'freeVar', name: 'y' } },
    { node: ahub, port: { kind: 'output' } },
  ])
  const b = new DiagramBuilder()
  // build in a DIFFERENT order so ids differ structurally
  const bhub = b.termNode(b.root, p('\\x. x'))
  const bn = b.termNode(b.root, p('y'))
  b.wire(b.root, [
    { node: bn, port: { kind: 'freeVar', name: 'y' } },
    { node: bhub, port: { kind: 'output' } },
  ])
  return { da: a.build(), db: b.build(), bn }
}

describe('composeActions', () => {
  it('preserves allocation exclusions and uses them while composing both sides', () => {
    const source = new DiagramBuilder().build()
    const target = new DiagramBuilder().build()
    const reserved = `${source.root}_intro`
    const tail: ProofAction[] = [{
      label: 'reserved introduction',
      steps: [{ rule: 'closedTermIntro', region: source.root, term: p('\\x. x') }],
      placements: [],
      allocation: { regions: [], nodes: [reserved], wires: [reserved] },
    }]

    const composed = composeActions(target, source, tail, ctx)
    const replayed = replayActions(target, composed, ctx)

    expect(composed[0]?.allocation).toEqual(tail[0]!.allocation)
    expect(Object.keys(replayed.nodes)).toEqual([`${reserved}_0`])
    expect(Object.keys(replayed.wires)).toEqual([`${reserved}_0`])
  })

  it('rewrites a backward tail onto the forward meet and replays end to end', () => {
    const { da, db, bn } = twoCopies()
    // backward tail (recorded against db): wrap the y-node in a double cut
    const tail = [action('wrap y', [{
      rule: 'doubleCutIntro',
      sel: mkSelection(db, { region: db.root, regions: [], nodes: [bn], wires: [] }),
    }])]
    const composed = composeActions(da, db, tail, ctx)
    const viaA = replayActions(da, composed, ctx)
    const viaB = replayActions(db, tail, ctx)
    expect(exploreForm(viaA)).toBe(exploreForm(viaB))
  })

  it('executes a polarity-sensitive backward tail in its recorded orientation', () => {
    const mk = () => {
      const h = new DiagramBuilder()
      const first = h.termNode(h.root, p('\\x. x'))
      const second = h.termNode(h.root, p('\\x. x'))
      const firstWire = h.wire(h.root, [{ node: first, port: { kind: 'output' } }])
      const secondWire = h.wire(h.root, [{ node: second, port: { kind: 'output' } }])
      return { d: h.build(), firstWire, secondWire }
    }
    const target = mk()
    const source = mk()
    const tail = [action('join at the root from the goal side', [{
      rule: 'wireJoin', a: source.firstWire, b: source.secondWire,
    }])]

    const composed = composeActions(target.d, source.d, tail, ctx, { orientation: 'backward' })
    const viaTarget = replayActions(target.d, composed, ctx, undefined, 'backward')
    const viaSource = replayActions(source.d, tail, ctx, undefined, 'backward')

    expect(exploreForm(viaTarget)).toBe(exploreForm(viaSource))
  })

  it('handles multi-step tails whose later steps reference ids created by earlier ones', () => {
    const { da, db, bn } = twoCopies()
    const wrapped = replayActions(db, [action('wrap y', [{
      rule: 'doubleCutIntro',
      sel: mkSelection(db, { region: db.root, regions: [], nodes: [bn], wires: [] }),
    }])], ctx)
    // find the new outer cut in the b-side result, then eliminate it again
    const outer = Object.entries(wrapped.regions)
      .find(([id, r]) => r.kind === 'cut' && db.regions[id] === undefined && r.parent === db.root)![0]
    const tail = [action('round trip wrapping', [
      { rule: 'doubleCutIntro', sel: mkSelection(db, { region: db.root, regions: [], nodes: [bn], wires: [] }) },
      { rule: 'doubleCutElim', region: outer },
    ])]
    const composed = composeActions(da, db, tail, ctx)
    const viaA = replayActions(da, composed, ctx)
    expect(exploreForm(viaA)).toBe(exploreForm(da))
  })

  it('preserves action groups while later actions map ids minted by a constituent step', () => {
    const { da, db, bn } = twoCopies()
    const wrapStep: ProofStep = {
      rule: 'doubleCutIntro',
      sel: mkSelection(db, { region: db.root, regions: [], nodes: [bn], wires: [] }),
    }
    const wrapped = replayActions(db, [action('find minted ids', [wrapStep])], ctx)
    const outer = Object.entries(wrapped.regions)
      .find(([id, region]) => db.regions[id] === undefined && region.kind === 'cut' && region.parent === db.root)![0]
    const inner = Object.entries(wrapped.regions)
      .find(([id, region]) => db.regions[id] === undefined && region.kind === 'cut' && region.parent === outer)![0]
    const tail = [
      action('wrap and annotate', [
        wrapStep,
        { rule: 'closedTermIntro', region: inner, term: p('\\x. x') },
      ], [{ introducedNode: 0, x: 12, y: 34 }]),
      action('remove minted cuts', [{ rule: 'doubleCutElim', region: outer }]),
    ]

    const composed = composeActions(da, db, tail, ctx)

    expect(composed.map(({ label, placements, steps }) => ({ label, placements, stepCount: steps.length })))
      .toEqual([
        { label: 'wrap and annotate', placements: [{ introducedNode: 0, x: 12, y: 34 }], stepCount: 2 },
        { label: 'remove minted cuts', placements: [], stepCount: 1 },
      ])
    expect(exploreForm(replayActions(da, composed, ctx)))
      .toBe(exploreForm(replayActions(db, tail, ctx)))
  })

  it('works across automorphic diagrams (two identical nodes)', () => {
    const mk = () => {
      const h = new DiagramBuilder()
      const n1 = h.termNode(h.root, p('\\x. x'))
      h.termNode(h.root, p('\\x. x'))
      return { d: h.build(), n1 }
    }
    const { d: da } = mk()
    const { d: db, n1: bn1 } = mk()
    const tail = [action('erase one copy', [{
      rule: 'erasure',
      sel: mkSelection(db, { region: db.root, regions: [], nodes: [bn1], wires: [] }),
    }])]
    const composed = composeActions(da, db, tail, ctx)
    const viaA = replayActions(da, composed, ctx)
    expect(Object.values(viaA.nodes)).toHaveLength(1)
  })

  it('uses ordered meet boundaries to disambiguate an automorphism', () => {
    const mk = () => {
      const h = new DiagramBuilder()
      const first = h.termNode(h.root, p('x'))
      const firstWire = h.wire(h.root, [{ node: first, port: { kind: 'freeVar', name: 'x' } }])
      const second = h.termNode(h.root, p('x'))
      const secondWire = h.wire(h.root, [{ node: second, port: { kind: 'freeVar', name: 'x' } }])
      return { d: h.build(), first, firstWire, second, secondWire }
    }
    const target = mk()
    const source = mk()
    const tail = [action('wrap the source boundary component', [{
      rule: 'doubleCutIntro',
      sel: mkSelection(source.d, {
        region: source.d.root, regions: [], nodes: [source.first], wires: [],
      }),
    }])]

    const composed = composeActions(target.d, source.d, tail, ctx, {
      boundaries: {
        target: [target.secondWire],
        source: [source.firstWire],
      },
    })

    expect(composed[0]!.steps[0]).toMatchObject({
      rule: 'doubleCutIntro',
      sel: { nodes: [target.second] },
    })
  })

  it('preserves repeated coalesced positions around a marker when mapping the next step', () => {
    const mk = () => {
      const h = new DiagramBuilder()
      const redundant = h.termNode(h.root, p('\\x. x'))
      const survivor = h.termNode(h.root, p('\\x. x'))
      const markerNode = h.termNode(h.root, p('\\x. x'))
      const drop = h.wire(h.root, [{ node: redundant, port: { kind: 'output' } }])
      const keep = h.wire(h.root, [{ node: survivor, port: { kind: 'output' } }])
      const marker = h.wire(h.root, [{ node: markerNode, port: { kind: 'output' } }])
      return { d: h.build(), redundant, survivor, markerNode, drop, keep, marker }
    }
    const target = mk()
    const source = mk()
    const certificate = { leftSteps: [], rightSteps: [] }
    const tail = [action('coalesce then wrap the unaffected marker', [
      {
        rule: 'anchoredWireContract',
        redundant: source.redundant,
        survivor: source.survivor,
        certificate,
      },
      {
        rule: 'doubleCutIntro',
        sel: mkSelection(source.d, {
          region: source.d.root, regions: [], nodes: [source.markerNode], wires: [],
        }),
      },
    ])]

    const closedComposition = composeActions(target.d, source.d, tail, ctx)
    expect(closedComposition[0]!.steps[1]).toMatchObject({
      rule: 'doubleCutIntro',
      sel: { nodes: [target.markerNode] },
    })

    const composed = composeActions(target.d, source.d, tail, ctx, {
      boundaries: {
        target: [target.drop, target.keep, target.drop, target.keep, target.marker],
        source: [source.marker, source.drop, source.marker, source.drop, source.keep],
      },
    })
    expect(composed[0]!.steps[1]).toMatchObject({
      rule: 'doubleCutIntro',
      sel: { nodes: [target.redundant] },
    })

    const viaTarget = replayActions(target.d, composed, ctx)
    const viaSource = replayActions(source.d, tail, ctx)
    expect(exploreForm(viaTarget, [
      target.drop, target.marker, target.drop, target.marker, target.marker,
    ])).toBe(exploreForm(viaSource, [
      source.marker, source.keep, source.marker, source.keep, source.keep,
    ]))
  })

  it('reports source-side boundary loss even when the corresponding target position is also lost', () => {
    const mk = () => {
      const h = new DiagramBuilder()
      const node = h.termNode(h.root, p('x'))
      const wire = h.wire(h.root, [{ node, port: { kind: 'freeVar', name: 'x' } }])
      return { d: h.build(), node, wire }
    }
    const target = mk()
    const source = mk()
    const tail = [action('erase the exposed component', [{
      rule: 'erasure',
      sel: mkSelection(source.d, {
        region: source.d.root, regions: [], nodes: [source.node], wires: [source.wire],
      }),
    }])]

    expect(() => composeActions(target.d, source.d, tail, ctx, {
      boundaries: {
        target: [target.wire],
        source: [source.wire],
      },
    })).toThrowError(/target boundary position 0.*source boundary position 0.*has no semantic image/)
  })

  it('maps erasure sel through the iso — erases the correct node in an asymmetric meet', () => {
    // Two distinguishable nodes: identity and a constant. Build the two copies
    // in DIFFERENT orders so ids are swapped (identity='n0' in db, identity='n1' in da).
    // The tail erases the identity node. Without id mapping, the composed step
    // references a db node id that exists in da but points to the CONSTANT node,
    // erasing the wrong node and producing a non-isomorphic result.
    const bA = new DiagramBuilder()
    bA.termNode(bA.root, p('\\a. \\b. a'))  // constant gets 'n0' in da
    bA.termNode(bA.root, p('\\x. x'))       // identity gets 'n1' in da
    const da = bA.build()

    const bB = new DiagramBuilder()
    const bn1 = bB.termNode(bB.root, p('\\x. x'))       // identity gets 'n0' in db
    bB.termNode(bB.root, p('\\a. \\b. a'))              // constant gets 'n1' in db
    const db = bB.build()

    const tail = [action('erase identity', [{
      rule: 'erasure',
      sel: mkSelection(db, { region: db.root, regions: [], nodes: [bn1], wires: [] }),
    }])]
    const composed = composeActions(da, db, tail, ctx)
    const viaA = replayActions(da, composed, ctx)
    const viaB = replayActions(db, tail, ctx)
    // Both results should have the constant node only
    expect(Object.values(viaA.nodes)).toHaveLength(1)
    // Fingerprints must match — the same (constant) node survives on both sides
    expect(exploreForm(viaA)).toBe(exploreForm(viaB))
  })

  it('maps comprehensionInstantiate binder targets through the iso', () => {
    // Marker-first vs marker-last builds give the ∃-chain DIFFERENT region
    // ids: db's rOuter id names the chain CUT in da. An unmapped binder
    // target therefore points at a cut — refused inside the composed replay —
    // while the mapped target lands on da's rOuter and the sides agree.
    const mk = (markerFirst: boolean) => {
      const h = new DiagramBuilder()
      const marker = () => {
        const c = h.cut(h.root)
        h.termNode(c, p('\\a. \\b. a'))
      }
      if (markerFirst) marker()
      const cut = h.cut(h.root)
      const rOuter = h.bubble(cut, 1)
      const rInner = h.bubble(rOuter, 1)
      const a = h.atom(rInner, rInner)
      const t = h.termNode(rInner, p('\\x. x'))
      h.wire(rInner, [
        { node: a, port: { kind: 'arg', index: 0 } },
        { node: t, port: { kind: 'output' } },
      ])
      if (!markerFirst) marker()
      return { d: h.build(), rOuter, rInner }
    }
    const { d: da } = mk(true)
    const { d: db, rOuter: bOuter, rInner: bInner } = mk(false)

    // the open comp "x : R′(x)"
    const c = new DiagramBuilder()
    const stub = c.bubble(c.root, 1)
    const atom = c.atom(stub, stub)
    const bx = c.wire(c.root, [{ node: atom, port: { kind: 'arg', index: 0 } }])
    const comp = mkDiagramWithBoundary(c.build(), [bx])

    const tail = [action('instantiate comprehension', [
      { rule: 'comprehensionInstantiate', bubble: bInner, comp, attachments: [], binders: { [stub]: bOuter } },
    ])]
    const composed = composeActions(da, db, tail, ctx)
    const viaA = replayActions(da, composed, ctx)
    const viaB = replayActions(db, tail, ctx)
    expect(exploreForm(viaA)).toBe(exploreForm(viaB))
  })

  it('maps comprehensionInstantiate parameter attachments through the iso', () => {
    // Marker-first vs marker-last builds shift the explicit wire ids: db's
    // parameter-wire id names the atom's ARG wire in da. That wire still
    // encloses the splice region, so an unmapped id would not be refused —
    // it would silently attach the copy's parameter port to the wrong wire,
    // which only the fingerprint comparison catches.
    const mk = (markerFirst: boolean) => {
      const h = new DiagramBuilder()
      const marker = () => {
        const c = h.cut(h.root)
        const m = h.termNode(c, p('\\a. \\b. a'))
        h.wire(c, [{ node: m, port: { kind: 'output' } }])
      }
      if (markerFirst) marker()
      const cut = h.cut(h.root)
      const bub = h.bubble(cut, 1)
      const a = h.atom(bub, bub)
      h.wire(cut, [{ node: a, port: { kind: 'arg', index: 0 } }])
      const wParam = h.wire(h.root, [])
      if (!markerFirst) marker()
      return { d: h.build(), bub, wParam }
    }
    const { d: da } = mk(true)
    const { d: db, bub: bBub, wParam: bParam } = mk(false)

    // parameterized comp: R(x) := "x —o— q", boundary [stub, parameter]
    const c = new DiagramBuilder()
    const n = c.termNode(c.root, p('q'))
    const wx = c.wire(c.root, [{ node: n, port: { kind: 'output' } }])
    const wq = c.wire(c.root, [{ node: n, port: { kind: 'freeVar', name: 'q' } }])
    const comp = mkDiagramWithBoundary(c.build(), [wx, wq])

    const tail = [action('instantiate parameterized comprehension', [
      { rule: 'comprehensionInstantiate', bubble: bBub, comp, attachments: [bParam], binders: {} },
    ])]
    const composed = composeActions(da, db, tail, ctx)
    const viaA = replayActions(da, composed, ctx)
    const viaB = replayActions(db, tail, ctx)
    expect(exploreForm(viaA)).toBe(exploreForm(viaB))
  })

  it('maps a closedTermIntro region through a NON-IDENTITY iso', () => {
    // Marker-first vs marker-last builds give the target cut DIFFERENT ids on
    // the two sides; an unmapped region id would introduce into the marker cut.
    const mk = (markerFirst: boolean) => {
      const h = new DiagramBuilder()
      const marker = () => {
        const c = h.cut(h.root)
        h.termNode(c, p('\\a. \\b. a'))
      }
      if (markerFirst) marker()
      const cut = h.cut(h.root)
      if (!markerFirst) marker()
      return { d: h.build(), cut }
    }
    const { d: da } = mk(true)
    const { d: db, cut: bCut } = mk(false)
    const tail = [action('introduce identity', [{ rule: 'closedTermIntro', region: bCut, term: p('\\x. x') }])]
    const composed = composeActions(da, db, tail, ctx)
    const viaA = replayActions(da, composed, ctx)
    const viaB = replayActions(db, tail, ctx)
    expect(exploreForm(viaA)).toBe(exploreForm(viaB))
  })

  it('refuses non-isomorphic meets by name', () => {
    const { da } = twoCopies()
    const other = new DiagramBuilder()
    other.termNode(other.root, p('y'))
    expect(() => composeActions(da, other.build(), [], ctx))
      .toThrowError(/do not meet/)
  })
})

describe('mapStepIds', () => {
  const certificate = { leftSteps: [], rightSteps: [] }

  it('preserves prototype-colliding conversion attachment names as own keys', () => {
    const attachments: Record<string, string> = Object.create(null) as Record<string, string>
    Object.defineProperties(attachments, {
      ['__proto__']: { value: 'w0', enumerable: true },
      constructor: { value: 'w1', enumerable: true },
      toString: { value: 'w2', enumerable: true },
    })
    const iso: DiagramIso = {
      regions: new Map(),
      nodes: new Map([['n0', 'N0']]),
      wires: new Map([['w0', 'W0'], ['w1', 'W1'], ['w2', 'W2']]),
    }

    const mapped = mapStepIds({
      rule: 'conversion', node: 'n0', term: p('x'), certificate,
      correspondence: { commonArity: 0, left: {}, right: {} }, attachments,
    }, iso)

    expect(mapped.rule).toBe('conversion')
    if (mapped.rule !== 'conversion') throw new Error('expected conversion step')
    expect(Object.getPrototypeOf(mapped.attachments)).toBeNull()
    expect(Object.keys(mapped.attachments)).toEqual(['__proto__', 'constructor', 'toString'])
    expect(mapped.attachments.__proto__).toBe('W0')
    expect(mapped.attachments.constructor).toBe('W1')
    expect(mapped.attachments.toString).toBe('W2')
  })

  it('remaps every anchored split host operand', () => {
    const iso: DiagramIso = {
      regions: new Map([['r0', 'R0']]),
      nodes: new Map([['n0', 'N0'], ['n1', 'N1']]),
      wires: new Map([['w0', 'W0']]),
    }
    expect(mapStepIds({
      rule: 'anchoredWireSplit', wire: 'w0', witness: 'n0',
      endpoints: [{ node: 'n1', port: { kind: 'arg', index: 0 } }], target: 'r0',
    }, iso)).toEqual({
      rule: 'anchoredWireSplit', wire: 'W0', witness: 'N0',
      endpoints: [{ node: 'N1', port: { kind: 'arg', index: 0 } }], target: 'R0',
    })
    expect(() => mapStepIds({
      rule: 'anchoredWireSplit', wire: 'missing', witness: 'n0',
      endpoints: [{ node: 'n1', port: { kind: 'arg', index: 0 } }], target: 'r0',
    }, iso)).toThrowError(/composition cannot map wire 'missing'/)
  })

  it('remaps both anchored contraction witnesses', () => {
    const iso: DiagramIso = {
      regions: new Map(),
      nodes: new Map([['n0', 'N0'], ['n1', 'N1']]),
      wires: new Map(),
    }
    expect(mapStepIds({
      rule: 'anchoredWireContract', redundant: 'n0', survivor: 'n1', certificate,
    }, iso)).toEqual({
      rule: 'anchoredWireContract', redundant: 'N0', survivor: 'N1', certificate,
    })
    expect(() => mapStepIds({
      rule: 'anchoredWireContract', redundant: 'n0', survivor: 'missing', certificate,
    }, iso)).toThrowError(/composition cannot map node 'missing'/)
  })

  it('remaps the region of a closedTermIntro step through the iso; the term is host-id-free', () => {
    const iso: DiagramIso = {
      regions: new Map([['r1', 'R1']]),
      nodes: new Map(),
      wires: new Map(),
    }
    expect(mapStepIds({ rule: 'closedTermIntro', region: 'r1', term: p('\\x. x') }, iso))
      .toEqual({ rule: 'closedTermIntro', region: 'R1', term: p('\\x. x') })
    expect(() => mapStepIds({ rule: 'closedTermIntro', region: 'missing', term: p('\\x. x') }, iso))
      .toThrowError(/cannot map region 'missing'/)
  })

  it('remaps comprehensionInstantiate attachments through iso.wires (order preserved)', () => {
    const b = new DiagramBuilder()
    const bn = b.termNode(b.root, p('\\x. x'))
    const bw = b.wire(b.root, [{ node: bn, port: { kind: 'output' } }])
    const pat = mkDiagramWithBoundary(b.build(), [bw])
    const iso: DiagramIso = {
      regions: new Map([['r1', 'R1']]),
      nodes: new Map(),
      wires: new Map([['w0', 'W0'], ['w1', 'W1']]),
    }
    expect(mapStepIds(
      { rule: 'comprehensionInstantiate', bubble: 'r1', comp: pat, attachments: ['w1', 'w0'], binders: {} },
      iso,
    )).toEqual({ rule: 'comprehensionInstantiate', bubble: 'R1', comp: pat, attachments: ['W1', 'W0'], binders: {} })
    expect(() => mapStepIds(
      { rule: 'comprehensionInstantiate', bubble: 'r1', comp: pat, attachments: ['missing'], binders: {} },
      iso,
    )).toThrowError(/cannot map wire 'missing'/)
  })

  it('remaps BOTH node ids of a headStrip step through the iso', () => {
    const iso: DiagramIso = {
      regions: new Map([['r0', 'R0']]),
      nodes: new Map([['n0', 'N0'], ['n1', 'N1']]),
      wires: new Map(),
    }
    const correspondence = { commonArity: 0, left: {}, right: {} }
    expect(mapStepIds({ rule: 'headStrip', a: 'n0', b: 'n1', correspondence }, iso))
      .toEqual({ rule: 'headStrip', a: 'N0', b: 'N1', correspondence })
    expect(() => mapStepIds({ rule: 'headStrip', a: 'n0', b: 'missing', correspondence }, iso))
      .toThrowError(/cannot map node 'missing'/)
  })

  it('remaps the node id of a relUnfold step through the iso', () => {
    const iso: DiagramIso = {
      regions: new Map(),
      nodes: new Map([['n0', 'N0']]),
      wires: new Map(),
    }
    expect(mapStepIds({ rule: 'relUnfold', node: 'n0' }, iso))
      .toEqual({ rule: 'relUnfold', node: 'N0' })
    expect(() => mapStepIds({ rule: 'relUnfold', node: 'missing' }, iso))
      .toThrowError(/cannot map node 'missing'/)
  })

  it('remaps a relFold step sel and args through the iso; defId is not mapped', () => {
    const iso: DiagramIso = {
      regions: new Map([['r0', 'R0']]),
      nodes: new Map([['n0', 'N0']]),
      wires: new Map([['w0', 'W0']]),
    }
    const sel = { region: 'r0', regions: [], nodes: ['n0'], wires: [] }
    expect(mapStepIds({ rule: 'relFold', sel, defId: 'nat', args: ['w0'] }, iso))
      .toEqual({ rule: 'relFold', sel: { region: 'R0', regions: [], nodes: ['N0'], wires: [] }, defId: 'nat', args: ['W0'] })
  })
})
