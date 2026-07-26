import { describe, expect, it } from 'vitest'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { exploreForm } from '../../../src/kernel/diagram/canonical/explore'
import type { DiagramIso } from '../../../src/kernel/diagram/canonical/explore'
import { IOTA, relSig } from '../../../src/kernel/diagram/sig'
import { mkSelection } from '../../../src/kernel/diagram/subgraph/selection'
import { replayActions, type ProofAction } from '../../../src/kernel/proof/action'
import { composeActions, mapStepIds } from '../../../src/kernel/proof/compose'
import { EMPTY_PROOF_CONTEXT } from '../../../src/kernel/proof/context'
import type { ProofStep } from '../../../src/kernel/proof/step'

function action(label: string, steps: readonly ProofStep[]): ProofAction {
  return { label, steps, placements: [] }
}

function asymmetricCopies() {
  const targetBuilder = new DiagramBuilder()
  const targetAtom = targetBuilder.atom(targetBuilder.root, relSig([]))
  targetBuilder.ref(targetBuilder.root, 'R', relSig([]))

  const sourceBuilder = new DiagramBuilder()
  sourceBuilder.ref(sourceBuilder.root, 'R', relSig([]))
  const sourceAtom = sourceBuilder.atom(sourceBuilder.root, relSig([]))

  return {
    target: targetBuilder.build(),
    targetAtom,
    source: sourceBuilder.build(),
    sourceAtom,
  }
}

describe('composeActions', () => {
  it('rewrites a structural tail across a non-identity isomorphism', () => {
    const copies = asymmetricCopies()
    const tail = [action('wrap the atom', [{
      rule: 'doubleCutIntro',
      sel: mkSelection(copies.source, {
        region: copies.source.root,
        regions: [],
        nodes: [copies.sourceAtom],
        wires: [],
      }),
    }])]

    const composed = composeActions(
      copies.target,
      copies.source,
      tail,
      EMPTY_PROOF_CONTEXT,
    )

    expect(composed[0]!.steps[0]).toMatchObject({
      rule: 'doubleCutIntro',
      sel: { nodes: [copies.targetAtom] },
    })
    expect(exploreForm(replayActions(
      copies.target,
      composed,
      EMPTY_PROOF_CONTEXT,
    ))).toBe(exploreForm(replayActions(
      copies.source,
      tail,
      EMPTY_PROOF_CONTEXT,
    )))
  })

  it('re-derives ids created by an earlier step in the same action', () => {
    const copies = asymmetricCopies()
    const wrap: ProofStep = {
      rule: 'doubleCutIntro',
      sel: mkSelection(copies.source, {
        region: copies.source.root,
        regions: [],
        nodes: [copies.sourceAtom],
        wires: [],
      }),
    }
    const wrapped = replayActions(
      copies.source,
      [action('probe', [wrap])],
      EMPTY_PROOF_CONTEXT,
    )
    const outer = Object.entries(wrapped.regions).find(
      ([id, region]) =>
        copies.source.regions[id] === undefined
        && region.kind === 'cut'
        && region.parent === copies.source.root,
    )![0]
    const tail = [action('round trip', [
      wrap,
      { rule: 'doubleCutElim', region: outer },
    ])]

    const composed = composeActions(
      copies.target,
      copies.source,
      tail,
      EMPTY_PROOF_CONTEXT,
    )

    expect(exploreForm(replayActions(
      copies.target,
      composed,
      EMPTY_PROOF_CONTEXT,
    ))).toBe(exploreForm(copies.target))
  })

  it('preserves action allocation exclusions', () => {
    const source = new DiagramBuilder().build()
    const target = new DiagramBuilder().build()
    const tail: ProofAction[] = [{
      label: 'reserved vacuity',
      steps: [{ rule: 'vacuousIntro', scope: source.root, sig: IOTA }],
      placements: [],
      allocation: { regions: ['dc'], nodes: ['n'], wires: ['r0_vac'] },
    }]

    const composed = composeActions(
      target,
      source,
      tail,
      EMPTY_PROOF_CONTEXT,
    )

    expect(composed[0]!.allocation).toEqual(tail[0]!.allocation)
    const replayed = replayActions(
      target,
      composed,
      EMPTY_PROOF_CONTEXT,
    )
    expect(Object.keys(replayed.wires)).toEqual(['r0_vac_0'])
  })

  it('uses ordered boundaries to disambiguate an automorphism', () => {
    const build = () => {
      const builder = new DiagramBuilder()
      const first = builder.ref(builder.root, 'R', relSig([IOTA]))
      const firstWire = builder.wire(builder.root, [{
        node: first,
        port: { kind: 'arg', index: 0 },
      }])
      const second = builder.ref(builder.root, 'R', relSig([IOTA]))
      const secondWire = builder.wire(builder.root, [{
        node: second,
        port: { kind: 'arg', index: 0 },
      }])
      return {
        diagram: builder.build(),
        first,
        firstWire,
        second,
        secondWire,
      }
    }
    const target = build()
    const source = build()
    const tail = [action('wrap pinned component', [{
      rule: 'doubleCutIntro',
      sel: mkSelection(source.diagram, {
        region: source.diagram.root,
        regions: [],
        nodes: [source.first],
        wires: [],
      }),
    }])]

    const composed = composeActions(
      target.diagram,
      source.diagram,
      tail,
      EMPTY_PROOF_CONTEXT,
      {
        boundaries: {
          target: [target.secondWire],
          source: [source.firstWire],
        },
      },
    )

    expect(composed[0]!.steps[0]).toMatchObject({
      rule: 'doubleCutIntro',
      sel: { nodes: [target.second] },
    })
  })

  it('reports boundary erasure on both sides', () => {
    const build = () => {
      const builder = new DiagramBuilder()
      const wire = builder.wire(builder.root, [], IOTA)
      return { diagram: builder.build(), wire }
    }
    const target = build()
    const source = build()
    const tail = [action('erase exposed wire', [{
      rule: 'vacuousElim',
      wireId: source.wire,
    }])]

    expect(() => composeActions(
      target.diagram,
      source.diagram,
      tail,
      EMPTY_PROOF_CONTEXT,
      {
        boundaries: {
          target: [target.wire],
          source: [source.wire],
        },
      },
    )).toThrowError(
      /target boundary position 0.*source boundary position 0.*no semantic image/,
    )
  })

  it('refuses non-isomorphic meets', () => {
    const copies = asymmetricCopies()
    const other = new DiagramBuilder().build()
    expect(() => composeActions(
      copies.target,
      other,
      [],
      EMPTY_PROOF_CONTEXT,
    )).toThrowError(/do not meet/)
  })
})

describe('mapStepIds', () => {
  const iso: DiagramIso = {
    regions: new Map([
      ['r0', 'R0'],
      ['r1', 'R1'],
      ['r2', 'R2'],
    ]),
    nodes: new Map([
      ['n0', 'N0'],
      ['n1', 'N1'],
      ['n2', 'N2'],
    ]),
    wires: new Map([
      ['w0', 'W0'],
      ['w1', 'W1'],
      ['w2', 'W2'],
    ]),
  }
  const selection = {
    region: 'r0',
    regions: ['r1'],
    nodes: ['n0'],
    wires: ['w0'],
  } as const
  const mappedSelection = {
    region: 'R0',
    regions: ['R1'],
    nodes: ['N0'],
    wires: ['W0'],
  } as const
  const retargets = [{
    boundary: 0,
    identity: 'n2',
    from: 'w1',
    to: 'w2',
  }] as const
  const mappedRetargets = [{
    boundary: 0,
    identity: 'N2',
    from: 'W1',
    to: 'W2',
  }] as const
  const certificate = {
    region: 'r0',
    regionMap: new Map([['pr0', 'r1']]),
    nodeMap: new Map([['pn0', 'n1']]),
    wireMap: new Map([['pw0', 'w1']]),
    attachments: ['w2'],
  } as const
  const mappedCertificate = {
    region: 'R0',
    regionMap: new Map([['pr0', 'R1']]),
    nodeMap: new Map([['pn0', 'N1']]),
    wireMap: new Map([['pw0', 'W1']]),
    attachments: ['W2'],
  } as const

  it('maps spawn, identity, and contradiction operands', () => {
    expect(mapStepIds({
      rule: 'refSpawn',
      region: 'r1',
      defId: 'R',
      sig: relSig([IOTA]),
    }, iso)).toEqual({
      rule: 'refSpawn',
      region: 'R1',
      defId: 'R',
      sig: relSig([IOTA]),
    })
    expect(mapStepIds({
      rule: 'atomSpawn',
      region: 'r1',
      wire: 'w0',
    }, iso)).toEqual({
      rule: 'atomSpawn',
      region: 'R1',
      wire: 'W0',
    })
    expect(mapStepIds({
      rule: 'identityInsert',
      region: 'r1',
      wires: ['w0', 'w1'],
    }, iso)).toEqual({
      rule: 'identityInsert',
      region: 'R1',
      wires: ['W0', 'W1'],
    })
    expect(mapStepIds({
      rule: 'identityContradiction',
      enclosingCut: 'r1',
      evidence: {
        equality: 'n0',
        disequalityCut: 'r2',
        disequality: 'n1',
      },
    }, iso)).toEqual({
      rule: 'identityContradiction',
      enclosingCut: 'R1',
      evidence: {
        equality: 'N0',
        disequalityCut: 'R2',
        disequality: 'N1',
      },
    })
  })

  it('maps selections, endpoints, certificates, and every retarget id', () => {
    expect(mapStepIds({
      rule: 'wireSever',
      wire: 'w0',
      keep: [{ node: 'n0', port: { kind: 'arg', index: 0 } }],
    }, iso)).toEqual({
      rule: 'wireSever',
      wire: 'W0',
      keep: [{ node: 'N0', port: { kind: 'arg', index: 0 } }],
    })
    expect(mapStepIds({
      rule: 'iteration',
      sel: selection,
      target: 'r1',
      retargets,
    }, iso)).toEqual({
      rule: 'iteration',
      sel: mappedSelection,
      target: 'R1',
      retargets: mappedRetargets,
    })
    expect(mapStepIds({
      rule: 'deiteration',
      sel: selection,
      justifier: selection,
      certificate,
      retargets,
    }, iso)).toEqual({
      rule: 'deiteration',
      sel: mappedSelection,
      justifier: mappedSelection,
      certificate: mappedCertificate,
      retargets: mappedRetargets,
    })
  })

  it('maps theorem, vacuity, fold, unfold, and structural operands', () => {
    expect(mapStepIds({
      rule: 'theorem',
      name: 'T',
      at: { sel: selection, args: ['w0', 'w1'] },
      direction: 'forward',
    }, iso)).toEqual({
      rule: 'theorem',
      name: 'T',
      at: { sel: mappedSelection, args: ['W0', 'W1'] },
      direction: 'forward',
    })
    expect(mapStepIds({
      rule: 'vacuousIntro',
      scope: 'r1',
      sig: IOTA,
    }, iso)).toEqual({
      rule: 'vacuousIntro',
      scope: 'R1',
      sig: IOTA,
    })
    expect(mapStepIds({
      rule: 'vacuousElim',
      wireId: 'w0',
    }, iso)).toEqual({
      rule: 'vacuousElim',
      wireId: 'W0',
    })
    expect(mapStepIds({
      rule: 'unfold',
      nodeId: 'n0',
    }, iso)).toEqual({
      rule: 'unfold',
      nodeId: 'N0',
    })
    expect(mapStepIds({
      rule: 'fold',
      occurrence: selection,
      args: ['w0'],
      defId: 'R',
    }, iso)).toEqual({
      rule: 'fold',
      occurrence: mappedSelection,
      args: ['W0'],
      defId: 'R',
    })
    expect(mapStepIds({
      rule: 'wireJoin',
      a: 'w0',
      b: 'w1',
    }, iso)).toEqual({
      rule: 'wireJoin',
      a: 'W0',
      b: 'W1',
    })
    expect(mapStepIds({
      rule: 'doubleCutElim',
      region: 'r1',
    }, iso)).toEqual({
      rule: 'doubleCutElim',
      region: 'R1',
    })
  })

  it('fails loudly when any host id is absent', () => {
    expect(() => mapStepIds({
      rule: 'identityContradiction',
      enclosingCut: 'r1',
      evidence: {
        equality: 'n0',
        disequalityCut: 'r2',
        disequality: 'missing',
      },
    }, iso)).toThrowError(/cannot map node 'missing'/)
  })
})
