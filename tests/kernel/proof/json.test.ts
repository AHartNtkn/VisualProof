import { describe, expect, it } from 'vitest'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { mkDiagramWithBoundary } from '../../../src/kernel/diagram/boundary'
import { exploreForm } from '../../../src/kernel/diagram/canonical/explore'
import { dwbFromJson, dwbToJson } from '../../../src/kernel/diagram/json'
import { IOTA, relSig } from '../../../src/kernel/diagram/sig'
import { extractSubgraph } from '../../../src/kernel/diagram/subgraph/extract'
import { mkSelection } from '../../../src/kernel/diagram/subgraph/selection'
import type { ProofAction } from '../../../src/kernel/proof/action'
import {
  actionFromJson,
  actionToJson,
  stepFromJson,
  stepToJson,
  theoremFromJson,
  theoremToJson,
} from '../../../src/kernel/proof/json'
import type { ProofStep } from '../../../src/kernel/proof/step'
import type { Theorem } from '../../../src/kernel/proof/theorem'

function roundTrip(step: ProofStep): void {
  const encoded = JSON.parse(JSON.stringify(stepToJson(step)))
  expect(stepFromJson(encoded)).toEqual(step)
}

const selection = {
  region: 'r0',
  regions: ['r1'],
  nodes: ['n0'],
  wires: ['w0'],
} as const

const occurrenceCertificate = {
  region: 'r0',
  regionMap: new Map([['root', 'r0']]),
  nodeMap: new Map([['pn0', 'n1']]),
  wireMap: new Map([['pw0', 'w1']]),
  attachments: ['w1'],
} as const

function boundedIdentity(swap: boolean) {
  const builder = new DiagramBuilder()
  const cut = builder.cut(builder.root)
  const identity = builder.identity(cut, IOTA, 2)
  builder.wire( [
    { node: identity, port: { kind: 'identity', index: swap ? 1 : 0 } },
  ])
  builder.wire( [
    { node: identity, port: { kind: 'identity', index: swap ? 0 : 1 } },
  ])
  const diagram = builder.build()
  return extractSubgraph(diagram, mkSelection(diagram, {
    region: cut,
    regions: [],
    nodes: [identity],
    wires: [],
  })).pattern
}

describe('action allocation JSON', () => {
  it('round-trips non-logical allocation exclusions', () => {
    const action: ProofAction = {
      label: 'reserved replay',
      steps: [{ rule: 'atomSpawn', region: 'r0', wire: 'w0' }],
      placements: [],
      allocation: { regions: ['dc'], nodes: ['atom'], wires: ['head'] },
    }

    const json = JSON.parse(JSON.stringify(actionToJson(action)))

    expect(json.allocation).toEqual(action.allocation)
    expect(actionFromJson(json)).toEqual(action)
  })

  it('omits empty allocation metadata', () => {
    const action: ProofAction = {
      label: 'ordinary replay',
      steps: [{ rule: 'atomSpawn', region: 'r0', wire: 'w0' }],
      placements: [],
      allocation: { regions: [], nodes: [], wires: [] },
    }

    expect(actionToJson(action)).toEqual({
      label: action.label,
      steps: [{ rule: 'atomSpawn', region: 'r0', wire: 'w0' }],
      placements: [],
    })
  })

  it('rejects duplicate allocation exclusions', () => {
    expect(() => actionFromJson({
      label: 'bad reservation',
      steps: [{ rule: 'atomSpawn', region: 'r0', wire: 'w0' }],
      placements: [],
      allocation: { regions: [], nodes: ['n0', 'n0'], wires: [] },
    })).toThrowError(/duplicate.*node.*n0/i)
  })
})

describe('step JSON', () => {
  it('round-trips the durable iteration payload with its selected root wire', () => {
    const builder = new DiagramBuilder()
    const node = builder.atom(builder.root, relSig([IOTA]))
    const wire = builder.wire( [
      { node, port: { kind: 'arg', index: 0 } },
    ])
    const diagram = builder.build()
    const step: ProofStep = {
      rule: 'iteration',
      sel: mkSelection(diagram, {
        region: diagram.root,
        regions: [],
        nodes: [node],
        wires: [wire],
      }),
      target: diagram.root,
    }

    const encoded = JSON.parse(JSON.stringify(stepToJson(step)))
    expect(encoded).toEqual({
      rule: 'iteration',
      sel: {
        region: diagram.root,
        regions: [],
        nodes: [node],
        wires: [wire],
      },
      target: diagram.root,
    })
    expect(stepFromJson(encoded)).toEqual(step)
  })

  it('round-trips every final Phase-1 primitive', () => {
    const steps: ProofStep[] = [
      { rule: 'refSpawn', region: 'r1', defId: 'nat', sig: relSig([IOTA]) },
      { rule: 'atomSpawn', region: 'r1', wire: 'w0' },
      { rule: 'identityInsert', region: 'r1', wires: ['w0', 'w1'] },
      {
        rule: 'wireJoin',
        input: { a: 'w0', b: 'w1' },
      },
      { rule: 'erasure', sel: selection },
      {
        rule: 'wireSever',
        input: {
          wire: 'w0',
          keep: [{ node: 'n0', port: { kind: 'arg', index: 0 } }],
        },
      },
      {
        rule: 'wireSever',
        input: {
          wire: 'w0',
          keep: [],
          scope: 'r1',
        },
      },
      { rule: 'iteration', sel: selection, target: 'r1' },
      {
        rule: 'deiteration',
        sel: selection,
        justifier: selection,
        certificate: occurrenceCertificate,
      },
      { rule: 'doubleCutIntro', sel: selection },
      { rule: 'doubleCutElim', region: 'r1' },
      {
        rule: 'theorem',
        name: 'dropQ',
        at: { sel: selection, args: ['w0'] },
        direction: 'reverse',
      },
      { rule: 'vacuousIntro', scope: 'r1', sig: IOTA },
      { rule: 'vacuousElim', wireId: 'w0' },
      { rule: 'unfold', nodeId: 'n0' },
      {
        rule: 'fold',
        occurrence: selection,
        args: ['w0'],
        defId: 'nat',
      },
      { rule: 'cutWrap', wire: 'w0' },
      { rule: 'cutAbsorb', wire: 'w0' },
      { rule: 'parallelSplit', wire: 'w0' },
      { rule: 'parallelFuse', a: 'w0', b: 'w1' },
      { rule: 'endsDelete', wire: 'w0' },
      {
        rule: 'endsSpawn',
        wire: 'w0',
        sites: [
          { region: 'r1', args: ['w1'] },
          { region: 'r0', args: ['w2'] },
        ],
      },
      { rule: 'arityShift', wire: 'w0', newArgSig: relSig([IOTA]) },
      { rule: 'arityUnshift', wire: 'w0', position: 2 },
      { rule: 'argPermute', wire: 'w0', permutation: [1, 0] },
      { rule: 'argDuplicate', wire: 'w0', position: 0 },
      { rule: 'argContract', wire: 'w0', position: 0 },
      { rule: 'argDrop', wire: 'w0', position: 1 },
      {
        rule: 'argExtend',
        wire: 'w0',
        position: 1,
        newArgSig: IOTA,
        attachments: { n0: 'w1', n1: 'w2' },
      },
      { rule: 'applyFormal', wire: 'w0', position: 0 },
      { rule: 'abstractFormal', ends: ['n0', 'n1'], scope: 'r1' },
      { rule: 'identityLeaf', wire: 'w0' },
      { rule: 'identityAbstract', nodes: ['n0'], scope: 'r0' },
      { rule: 'refLeaf', wire: 'w0', defId: 'nat' },
      { rule: 'refAbstract', nodes: ['n0', 'n1'], scope: 'r1' },
    ]

    for (const step of steps) roundTrip(step)
  })

  it('rejects invented serialized reification authority on refSpawn', () => {
    expect(() => stepFromJson({
      rule: 'refSpawn',
      region: 'r0',
      defId: 'truthReification',
      sig: relSig([relSig([])]),
      reification: true,
    })).toThrowError(/refSpawn step has unknown field 'reification'/i)
  })

  it('strictly rejects displaced wire shapes and malformed content occurrences', () => {
    expect(() => stepFromJson({
      rule: 'wireJoin',
      a: 'w0',
      b: 'w1',
    })).toThrowError(/wireJoin step has unknown field 'a'/i)
    expect(() => stepFromJson({
      rule: 'wireSever',
      wire: 'w0',
      keep: [],
    })).toThrowError(/wireSever step has unknown field 'wire'/i)
    expect(() => stepFromJson({
      rule: 'wireJoin',
      input: {
        a: 'w0',
        b: 'w1',
        wire: 'displaced',
      },
    })).toThrowError(/wireJoin input has unknown field 'wire'/i)
    expect(() => stepFromJson({
      rule: 'wireSever',
      input: {
        kind: 'iota',
        wire: 'w0',
        keep: [],
      },
    })).toThrowError(/wireSever input has unknown field 'kind'/i)
    expect(() => stepFromJson({
      rule: 'wireJoin',
      input: {
        kind: 'relation',
        wire: 'w0',
        content: {},
        parameters: [],
      },
    })).toThrowError(/wireJoin input has unknown field 'kind'/i)
  })

  it('omits obsolete term certificates from occurrence-certificate JSON', () => {
    const encoded = stepToJson({
      rule: 'deiteration',
      sel: selection,
      justifier: selection,
      certificate: occurrenceCertificate,
      }) as {
      certificate: Record<string, unknown>
    }

    expect(encoded.certificate).toEqual({
      region: 'r0',
      regionMap: [['root', 'r0']],
      nodeMap: [['pn0', 'n1']],
      wireMap: [['pw0', 'w1']],
      attachments: ['w1'],
    })
    expect(encoded.certificate).not.toHaveProperty('termCertificates')
  })

  it('rejects every removed proof-rule string', () => {
    for (const rule of [
      'openTermSpawn', 'relationSpawn', 'boundRelationSpawn',
      'inconsistentCutElim', 'conversion', 'congruenceJoin',
      'identityContradiction',
      'anchoredWireSplit', 'anchoredWireContract', 'headStrip',
      'closedTermIntro', 'fusion', 'fission',
      'bodyAttach', 'bodyDetach',
    ]) {
      expect(() => stepFromJson({ rule })).toThrow(/unknown rule/)
    }
  })

  it('strictly validates final primitive carriers', () => {
    expect(() => stepFromJson({ rule: 'nonsense' })).toThrowError(/unknown rule/)
    expect(() => stepFromJson({
      rule: 'atomSpawn', region: 'r0', wire: 'w0', extra: true,
    })).toThrowError(/unknown field 'extra'/)
    expect(() => stepFromJson({
      rule: 'identityInsert', region: 'r0', wires: 'w0',
    })).toThrowError(/wires must be an array/)
    expect(() => stepFromJson({
      rule: ['identity', 'Contradiction'].join(''),
      enclosingCut: 'r1',
      evidence: { equality: 'n0', disequalityCut: 'r2', disequality: 'n1' },
    })).toThrowError(/unknown rule/)
    expect(() => stepFromJson({
      rule: 'iteration',
      sel: selection,
      target: 'r1',
      retargets: [],
    })).toThrowError(/iteration step/)
    expect(() => stepFromJson({
      rule: 'deiteration',
      sel: selection,
      justifier: selection,
      certificate: {
        region: 'r0',
        regionMap: [],
        nodeMap: [],
        wireMap: [],
        attachments: [],
        termCertificates: [],
      },
      })).toThrowError(/unknown field 'termCertificates'/)
    expect(() => stepFromJson({
      rule: 'vacuousIntro',
      sig: { kind: 'iota' },
      body: {},
    })).toThrowError(/unknown field 'body'/)
    expect(() => stepFromJson({
      rule: 'fold',
      occurrence: selection,
      args: ['w0'],
      target: { defId: 'legacy' },
    })).toThrowError(/unknown field 'target'/)
  })
})

describe('diagram-with-boundary JSON', () => {
  it('round-trips bounded identity structure for both storage permutations', () => {
    const decoded = [false, true].map((swap) => {
      const body = boundedIdentity(swap)
      const result = dwbFromJson(JSON.parse(JSON.stringify(dwbToJson(body))))
      expect(result.boundary).toHaveLength(2)
      expect(new Set(result.boundary).size).toBe(2)
      expect(Object.values(result.diagram.nodes)).toContainEqual({
        kind: 'identity',
        region: result.diagram.root,
        sig: IOTA,
        arity: 2,
      })
      return exploreForm(result.diagram, result.boundary)
    })

    expect(decoded[1]).toBe(decoded[0])
  })

  it('round-trips repeated boundary positions without collapsing arity', () => {
    const builder = new DiagramBuilder()
    const wire = builder.wire( [], IOTA)
    const aliased = mkDiagramWithBoundary(builder.build(), [wire, wire])
    const decoded = dwbFromJson(JSON.parse(JSON.stringify(dwbToJson(aliased))))

    expect(decoded.boundary).toEqual([wire, wire])
  })

  it('round-trips and re-enforces the root-scoped-boundary invariant', () => {
    const builder = new DiagramBuilder()
    const bare = builder.wire( [], IOTA)
    const dwb = mkDiagramWithBoundary(builder.build(), [bare])
    const decoded = dwbFromJson(JSON.parse(JSON.stringify(dwbToJson(dwb))))

    expect(decoded.boundary).toEqual([bare])
    const encoded = JSON.parse(JSON.stringify(dwbToJson(dwb))) as {
      diagram: {
        root: string
        regions: Record<string, unknown>
        wires: Record<string, { scope: string }>
      }
      boundary: string[]
    }
    encoded.diagram.regions.r1 = { kind: 'cut', parent: encoded.diagram.root }
    encoded.diagram.wires[encoded.boundary[0]!]!.scope = 'r1'
    expect(() => dwbFromJson(encoded)).toThrowError(/must be scoped at the diagram root/)
  })

  it('includes the supplied context when a boundary wire is missing', () => {
    const builder = new DiagramBuilder()
    const diagram = builder.build()
    const serialized = {
      diagram: {
        root: diagram.root,
        regions: diagram.regions,
        nodes: diagram.nodes,
        wires: diagram.wires,
      },
      boundary: ['missing'],
    }

    expect(() => dwbFromJson(serialized, "relation 'myRel'"))
      .toThrowError(/relation 'myRel'/)
  })
})

describe('theorem JSON', () => {
  it('persists gesture actions and ordered ref boundaries', () => {
    const builder = new DiagramBuilder()
    const ref = builder.ref(builder.root, 'R', relSig([IOTA]))
    const boundary = builder.wire( [{
      node: ref,
      port: { kind: 'arg', index: 0 },
    }])
    const side = mkDiagramWithBoundary(builder.build(), [boundary])
    const theorem: Theorem = {
      name: 'noop',
      lhs: side,
      rhs: side,
      actions: [{
        label: 'introduce two cuts',
        steps: [
          {
            rule: 'doubleCutIntro',
            sel: { region: side.diagram.root, regions: [], nodes: [], wires: [] },
          },
          { rule: 'doubleCutElim', region: 'dc' },
        ],
        placements: [{ introducedNode: 0, x: 12, y: -4 }],
      }],
    }

    const encoded = JSON.parse(JSON.stringify(theoremToJson(theorem)))
    const decoded = theoremFromJson(encoded)

    expect(decoded.name).toBe('noop')
    expect(decoded.lhs.boundary).toEqual([boundary])
    expect(decoded.actions).toEqual(theorem.actions)
  })

  it('rejects obsolete flat theorem fields and nested extras', () => {
    const builder = new DiagramBuilder()
    const side = dwbToJson(mkDiagramWithBoundary(builder.build(), []))
    expect(() => theoremFromJson({
      name: 'old', lhs: side, rhs: side, actions: [], steps: [],
    })).toThrowError(/unknown field 'steps'/)

    const theorem: Theorem = {
      name: 'strict',
      lhs: mkDiagramWithBoundary(builder.build(), []),
      rhs: mkDiagramWithBoundary(builder.build(), []),
      actions: [{
        label: 'strict action',
        steps: [{
          rule: 'doubleCutIntro',
          sel: { region: builder.root, regions: [], nodes: [], wires: [] },
        }],
        placements: [{ introducedNode: 0, x: 1, y: 2 }],
      }],
    }
    const valid = theoremToJson(theorem) as {
      actions: Array<{
        steps: Array<Record<string, unknown>>
        placements: Array<Record<string, unknown>>
      }>
    }
    expect(() => theoremFromJson({
      ...valid,
      actions: [{ ...valid.actions[0]!, extra: true }],
    })).toThrowError(/action.*unknown field 'extra'/)
    expect(() => theoremFromJson({
      ...valid,
      actions: [{
        ...valid.actions[0]!,
        steps: [{ ...valid.actions[0]!.steps[0]!, extra: true }],
      }],
    })).toThrowError(/step has unknown field 'extra'/)
    expect(() => theoremFromJson({
      ...valid,
      actions: [{
        ...valid.actions[0]!,
        placements: [{ ...valid.actions[0]!.placements[0]!, extra: true }],
      }],
    })).toThrowError(/placement.*unknown field 'extra'/)
  })
})
