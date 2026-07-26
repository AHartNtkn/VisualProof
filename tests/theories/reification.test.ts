import { createHash } from 'node:crypto'
import { readFileSync, readdirSync } from 'node:fs'
import { fileURLToPath } from 'node:url'
import { describe, expect, it } from 'vitest'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { exploreForm } from '../../src/kernel/diagram/canonical/explore'
import type { DiagramWithBoundary } from '../../src/kernel/diagram/boundary'
import type {
  Diagram,
  NodeId,
  RegionId,
  WireId,
} from '../../src/kernel/diagram/diagram'
import { dwbToJson } from '../../src/kernel/diagram/json'
import { IOTA, relSig, sigKey } from '../../src/kernel/diagram/sig'
import { verifyTheory } from '../../src/kernel/proof/context'
import type { ProofStep } from '../../src/kernel/proof/step'
import {
  atom,
  biconditional,
  declareWire,
  emptyGraph,
  finishDiagram,
  finishDiagramWithBoundary,
  identity,
  implication,
  quantifierScope,
  ref,
} from '../../src/theories/graph'
import {
  PrimitiveStepRecorder,
  onlyNewCut,
  onlyNewNode,
  onlyNewWire,
} from '../../src/theories/record'
import {
  associativityInductionReification,
  commutativityInductionReification,
  rightIdentityInductionReification,
  successorShiftInductionReification,
  truthReification,
} from '../../src/theories/reification'
import { buildFregeTheory } from '../../src/theories'

function binaryReification() {
  let graph = emptyGraph()
  const pResult = declareWire(graph, graph.root, relSig([IOTA, IOTA]))
  graph = pResult.graph
  const p = pResult.value
  const sourceResult = declareWire(graph, graph.root, relSig([IOTA, IOTA]))
  graph = sourceResult.graph
  const source = sourceResult.value
  const quantified = quantifierScope(graph, graph.root, 'forall', [IOTA, IOTA])
  graph = quantified.graph
  const [x, y] = quantified.value.variables
  const iff = biconditional(graph, quantified.value.body)
  graph = iff.graph

  for (const [region, relation] of [
    [iff.value.forward.antecedent, p],
    [iff.value.forward.consequent, source],
    [iff.value.reverse.antecedent, source],
    [iff.value.reverse.consequent, p],
  ] as const) {
    graph = atom(graph, region, relation, [x!, y!]).graph
  }
  return finishDiagramWithBoundary(graph, [p, source])
}

function witnessAtoms(
  definition: ReturnType<typeof truthReification>,
): readonly string[] {
  const witness = definition.boundary[0]!
  return definition.diagram.wires[witness]!.endpoints
    .filter((endpoint) => endpoint.port.kind === 'head')
    .map((endpoint) => endpoint.node)
}

function exactOne<T>(values: readonly T[], what: string): T {
  expect(values, what).toHaveLength(1)
  return values[0]!
}

function directCuts(diagram: Diagram, parent: RegionId): readonly RegionId[] {
  return Object.entries(diagram.regions)
    .filter(([, region]) => region.kind === 'cut' && region.parent === parent)
    .map(([id]) => id)
}

function directNodes(diagram: Diagram, region: RegionId): readonly NodeId[] {
  return Object.entries(diagram.nodes)
    .filter(([, node]) => node.region === region)
    .map(([id]) => id)
}

function scopedWires(diagram: Diagram, region: RegionId): readonly WireId[] {
  return Object.entries(diagram.wires)
    .filter(([, wire]) => wire.scope === region)
    .map(([id]) => id)
}

function endpointWire(
  diagram: Diagram,
  node: NodeId,
  kind: 'head' | 'arg' | 'identity',
  index?: number,
): WireId {
  return exactOne(
    Object.entries(diagram.wires)
      .filter(([, wire]) => wire.endpoints.some((endpoint) =>
        endpoint.node === node
        && endpoint.port.kind === kind
        && (
          kind === 'head'
          || (
            endpoint.port.kind !== 'head'
            && endpoint.port.index === index
          )
        )))
      .map(([id]) => id),
    `one ${kind}${index === undefined ? '' : ` ${index}`} wire for '${node}'`,
  )
}

type ReificationSkeleton = {
  readonly variables: readonly WireId[]
  readonly materialSites: readonly [
    { readonly region: RegionId; readonly excludedCuts: readonly RegionId[] },
    { readonly region: RegionId; readonly excludedCuts: readonly RegionId[] },
  ]
}

function assertReificationSkeleton(
  definition: DiagramWithBoundary,
  arity: number,
): ReificationSkeleton {
  const { diagram } = definition
  const witness = definition.boundary[0]!
  const witnessSig = diagram.wires[witness]!.sig
  expect(witnessSig).toEqual(relSig(
    Array.from({ length: arity }, () => IOTA),
  ))

  let body = diagram.root
  let variables: readonly WireId[] = []
  if (arity > 0) {
    const universal = exactOne(
      directCuts(diagram, diagram.root),
      'one outer universal cut',
    )
    body = exactOne(
      directCuts(diagram, universal),
      'one positive universal body',
    )
    variables = scopedWires(diagram, universal)
    expect(variables).toHaveLength(arity)
    expect(variables.map((wire) => sigKey(diagram.wires[wire]!.sig)))
      .toEqual(Array.from({ length: arity }, () => 'i'))
  }

  const implications = directCuts(diagram, body)
  expect(implications, 'the two biconditional implication cuts').toHaveLength(2)
  const witnessNodes = witnessAtoms(definition)
  expect(witnessNodes).toHaveLength(2)
  const forward = exactOne(
    implications.filter((antecedent) =>
      witnessNodes.some((node) => diagram.nodes[node]!.region === antecedent)),
    'one P-to-S implication',
  )
  const forwardConsequent = exactOne(
    directCuts(diagram, forward),
    'one P-to-S consequent',
  )
  const reverse = exactOne(
    implications.filter((antecedent) => antecedent !== forward),
    'one S-to-P implication',
  )
  const reverseConsequent = exactOne(
    directCuts(diagram, reverse).filter((candidate) =>
      witnessNodes.some((node) => diagram.nodes[node]!.region === candidate)),
    'one S-to-P consequent containing P',
  )

  const expectedWitnessRegions = [
    forward,
    reverseConsequent,
  ].sort()
  expect(witnessNodes.map((node) => diagram.nodes[node]!.region).sort())
    .toEqual(expectedWitnessRegions)
  for (const node of witnessNodes) {
    expect(diagram.nodes[node]).toMatchObject({ kind: 'atom', sig: witnessSig })
    expect(Array.from({ length: arity }, (_, index) =>
      endpointWire(diagram, node, 'arg', index)))
      .toEqual(variables)
  }

  return {
    variables,
    materialSites: [
      { region: forwardConsequent, excludedCuts: [] },
      { region: reverse, excludedCuts: [reverseConsequent] },
    ],
  }
}

function nodeDescriptor(
  diagram: Diagram,
  nodeId: NodeId,
  labels: ReadonlyMap<WireId, string>,
): string {
  const node = diagram.nodes[nodeId]!
  const label = (wire: WireId): string => {
    const value = labels.get(wire)
    if (value === undefined) throw new Error(`missing test label for wire '${wire}'`)
    return value
  }
  if (node.kind === 'atom') {
    const head = label(endpointWire(diagram, nodeId, 'head'))
    const args = node.sig.args.map((_, index) =>
      label(endpointWire(diagram, nodeId, 'arg', index)))
    return `${head}(${args.join(',')})`
  }
  if (node.kind === 'identity') {
    const args = Array.from({ length: node.arity }, (_, index) =>
      label(endpointWire(diagram, nodeId, 'identity', index))).sort()
    return `=(${args.join(',')})`
  }
  throw new Error(`unexpected ref '${nodeId}' in reified material`)
}

type MaterialExpectation = {
  readonly captureNames: readonly string[]
  readonly mainNames: readonly string[]
  readonly localNames: readonly string[]
  readonly premises: readonly string[]
  readonly conclusions: readonly string[]
  readonly canonicalHash: string
}

function assertInductionMaterial(
  definition: DiagramWithBoundary,
  expected: MaterialExpectation,
): void {
  const skeleton = assertReificationSkeleton(
    definition,
    expected.mainNames.length,
  )
  const baseLabels = new Map<WireId, string>()
  definition.boundary.forEach((wire, index) => {
    baseLabels.set(wire, index === 0 ? 'P' : expected.captureNames[index - 1]!)
  })
  skeleton.variables.forEach((wire, index) => {
    baseLabels.set(wire, expected.mainNames[index]!)
  })

  for (const materialSite of skeleton.materialSites) {
    const materialRegion = materialSite.region
    expect(directNodes(definition.diagram, materialRegion)).toEqual([])
    const universal = exactOne(
      directCuts(definition.diagram, materialRegion)
        .filter((cut) => !materialSite.excludedCuts.includes(cut)),
      'one local universal cut in S',
    )
    const localVariables = scopedWires(definition.diagram, universal)
    expect(localVariables).toHaveLength(expected.localNames.length)
    expect(localVariables.map((wire) =>
      sigKey(definition.diagram.wires[wire]!.sig)))
      .toEqual(expected.localNames.map(() => 'i'))
    const labels = new Map(baseLabels)
    localVariables.forEach((wire, index) => {
      labels.set(wire, expected.localNames[index]!)
    })

    const universalBody = exactOne(
      directCuts(definition.diagram, universal),
      'one positive local universal body',
    )
    const implicationCut = exactOne(
      directCuts(definition.diagram, universalBody),
      'one material implication',
    )
    const conclusionCut = exactOne(
      directCuts(definition.diagram, implicationCut),
      'one material conclusion',
    )
    expect(directCuts(definition.diagram, conclusionCut)).toEqual([])
    expect(directNodes(definition.diagram, universal)).toEqual([])
    expect(directNodes(definition.diagram, universalBody)).toEqual([])

    const premises = directNodes(definition.diagram, implicationCut)
      .map((node) => nodeDescriptor(definition.diagram, node, labels))
      .sort()
    const conclusions = directNodes(definition.diagram, conclusionCut)
      .map((node) => nodeDescriptor(definition.diagram, node, labels))
      .sort()
    expect(premises).toEqual([...expected.premises].sort())
    expect(conclusions).toEqual([...expected.conclusions].sort())
  }

  const canonical = exploreForm(definition.diagram, definition.boundary)
  expect(createHash('sha256').update(canonical).digest('hex'))
    .toBe(expected.canonicalHash)
}

describe('explicit grammatical relation reification', () => {
  it('constructs nullary Truth deterministically with canonical JSON', () => {
    const first = truthReification()
    const second = truthReification()

    expect(dwbToJson(first)).toEqual(dwbToJson(second))
    expect(exploreForm(first.diagram, first.boundary))
      .toBe(exploreForm(second.diagram, second.boundary))
    expect(dwbToJson(first)).toEqual({
      diagram: {
        root: 'r0',
        regions: {
          r0: { kind: 'sheet' },
          r1: { kind: 'cut', parent: 'r0' },
          r2: { kind: 'cut', parent: 'r1' },
          r3: { kind: 'cut', parent: 'r0' },
          r4: { kind: 'cut', parent: 'r3' },
        },
        nodes: {
          n0: { kind: 'atom', region: 'r1', sig: { kind: 'rel', args: [] } },
          n1: { kind: 'atom', region: 'r4', sig: { kind: 'rel', args: [] } },
        },
        wires: {
          w0: {
            scope: 'r0',
            sig: { kind: 'rel', args: [] },
            endpoints: [
              { node: 'n0', port: 'hd' },
              { node: 'n1', port: 'hd' },
            ],
          },
        },
      },
      boundary: ['w0'],
    })
  })

  it('reifies arities zero, one, and two with a homogeneous witness', () => {
    const definitions = [
      truthReification(),
      rightIdentityInductionReification(),
      binaryReification(),
    ] as const

    definitions.forEach((definition, arity) => {
      const witness = definition.boundary[0]!
      const sig = definition.diagram.wires[witness]!.sig
      expect(sig.kind).toBe('rel')
      expect(sigKey(sig)).toBe(sigKey(relSig(
        Array.from({ length: arity }, () => IOTA),
      )))
      const atoms = witnessAtoms(definition)
      expect(atoms).toHaveLength(2)
      for (const node of atoms) {
        expect(definition.diagram.nodes[node]).toMatchObject({
          kind: 'atom',
          sig,
        })
      }
    })

    const binary = definitions[2]
    expect(binary.boundary.map((wire) =>
      sigKey(binary.diagram.wires[wire]!.sig)))
      .toEqual(['(i,i)', '(i,i)'])
    const quantifiedIndividuals = Object.entries(binary.diagram.wires)
      .filter(([wire]) => !binary.boundary.includes(wire))
    expect(quantifiedIndividuals).toHaveLength(2)
    expect(quantifiedIndividuals.every(([, wire]) =>
      sigKey(wire.sig) === 'i'
      && binary.diagram.regions[wire.scope]?.kind === 'cut'))
      .toBe(true)

    const binarySkeleton = assertReificationSkeleton(binary, 2)
    const binaryLabels = new Map<WireId, string>([
      [binary.boundary[0]!, 'P'],
      [binary.boundary[1]!, 'S'],
      [binarySkeleton.variables[0]!, 'x'],
      [binarySkeleton.variables[1]!, 'y'],
    ])
    for (const site of binarySkeleton.materialSites) {
      expect(directCuts(binary.diagram, site.region)
        .filter((cut) => !site.excludedCuts.includes(cut))).toEqual([])
      expect(directNodes(binary.diagram, site.region).map((node) =>
        nodeDescriptor(binary.diagram, node, binaryLabels)))
        .toEqual(['S(x,y)'])
    }
    expect(createHash('sha256')
      .update(exploreForm(binary.diagram, binary.boundary))
      .digest('hex'))
      .toBe('808dc8740bba500f73b033e6973e2fe138e1f94f8fc4d036e891f6f4a9674995')
  })

  it('pins the complete canonical material of all four induction definitions', () => {
    const definitions = [
      [
        rightIdentityInductionReification(),
        ['(i)', '(i)', '(i,i,i)'],
        {
          captureNames: ['zero', 'plus'],
          mainNames: ['a'],
          localNames: ['z', 'o'],
          premises: ['zero(z)', 'plus(a,z,o)'],
          conclusions: ['=(a,o)'],
          canonicalHash: 'fed6393505522bff59af12af6815048a3ab4abec8dc1eb9529568ee43f28f954',
        },
      ],
      [
        associativityInductionReification(),
        ['(i)', '(i,i,i)'],
        {
          captureNames: ['plus'],
          mainNames: ['a'],
          localNames: ['b', 'c', 't', 'o', 'u'],
          premises: ['plus(a,b,t)', 'plus(t,c,o)', 'plus(b,c,u)'],
          conclusions: ['plus(a,u,o)'],
          canonicalHash: '3b0bd4c64e191839a14489f0ea9f133d04ea876423974b3476aa5a2679d8c27f',
        },
      ],
      [
        successorShiftInductionReification(),
        ['(i)', '(i,i)', '(i,i,i)'],
        {
          captureNames: ['succ', 'plus'],
          mainNames: ['a'],
          localNames: ['n', 'sn', 'o', 'so'],
          premises: ['succ(n,sn)', 'plus(a,n,o)', 'succ(o,so)'],
          conclusions: ['plus(a,sn,so)'],
          canonicalHash: 'abdac285ce7216036527d2b850ef4de63b42295091d0e844c001d56b48198712',
        },
      ],
      [
        commutativityInductionReification(),
        ['(i)', '(i,i,i)'],
        {
          captureNames: ['plus'],
          mainNames: ['a'],
          localNames: ['b', 'o'],
          premises: ['plus(a,b,o)'],
          conclusions: ['plus(b,a,o)'],
          canonicalHash: '76f8ad83aec3852923139c9ab4b522fee3b1dd45f5cff9e6ac1b86403432722a',
        },
      ],
    ] as const

    for (const [definition, signatures, material] of definitions) {
      expect(definition.boundary.map((wire) =>
        sigKey(definition.diagram.wires[wire]!.sig)))
        .toEqual(signatures)
      expect(witnessAtoms(definition)).toHaveLength(2)
      expect(definition.boundary.every((wire) =>
        definition.diagram.wires[wire]!.scope === definition.diagram.root
        && definition.diagram.wires[wire]!.endpoints.length > 0))
        .toBe(true)
      assertInductionMaterial(definition, material)
    }
  })

  it('preserves root-co-scoped equality between distinct boundary entries', () => {
    let graph = emptyGraph()
    const left = declareWire(graph, graph.root, IOTA)
    graph = left.graph
    const right = declareWire(graph, graph.root, IOTA)
    graph = right.graph
    const equality = identity(graph, graph.root, [left.value, right.value])
    graph = equality.graph

    const closed = finishDiagram(graph)
    const open = finishDiagramWithBoundary(
      graph,
      [left.value, right.value],
    )

    expect(closed.nodes[equality.value]).toBeUndefined()
    expect(Object.keys(closed.wires)).toEqual([left.value])
    expect(open.boundary).toEqual([left.value, right.value])
    expect(Object.keys(open.diagram.wires)).toEqual([left.value, right.value])
    expect(open.diagram.nodes[equality.value]).toEqual({
      kind: 'identity',
      region: graph.root,
      sig: IOTA,
      arity: 2,
    })
  })

  it('constructs typed refs and conditional identities directly as graph syntax', () => {
    let graph = emptyGraph()
    const left = declareWire(graph, graph.root, IOTA)
    graph = left.graph
    const right = declareWire(graph, graph.root, IOTA)
    graph = right.graph
    const claim = implication(graph, graph.root)
    graph = claim.graph
    graph = ref(
      graph,
      claim.value.antecedent,
      'binarySource',
      [left.value, right.value],
    ).graph
    graph = identity(
      graph,
      claim.value.consequent,
      [left.value, right.value],
    ).graph
    const definition = finishDiagramWithBoundary(
      graph,
      [left.value, right.value],
    )

    expect(Object.values(definition.diagram.nodes).map((node) => node.kind))
      .toEqual(['ref', 'identity'])
    expect(Object.values(definition.diagram.nodes)[0]).toMatchObject({
      kind: 'ref',
      sig: relSig([IOTA, IOTA]),
    })
  })

  it('spawns the same explicit definition at root and a nested legal scope', () => {
    const theory = buildFregeTheory()
    const context = verifyTheory(theory)
    const expectedSig = relSig([relSig([])])

    const rootStart = new DiagramBuilder().build()
    const rootRecorder = new PrimitiveStepRecorder(
      rootStart,
      context,
      'backward',
    )
    rootRecorder.record('spawn reified Truth at root', {
      rule: 'refSpawn',
      region: rootStart.root,
      defId: 'truthReification',
      sig: expectedSig,
    })
    const rootRef = onlyNewNode(rootStart, rootRecorder.diagram, rootStart.root)
    const rootWitness = onlyNewWire(rootStart, rootRecorder.diagram, rootStart.root)
    expect(rootRecorder.diagram.nodes[rootRef]).toMatchObject({
      kind: 'ref',
      defId: 'truthReification',
    })
    expect(sigKey(rootRecorder.diagram.wires[rootWitness]!.sig)).toBe('()')

    const nestedBuilder = new DiagramBuilder()
    const nested = nestedBuilder.cut(nestedBuilder.root)
    const nestedStart = nestedBuilder.build()
    const nestedRecorder = new PrimitiveStepRecorder(nestedStart, context)
    nestedRecorder.record('spawn reified Truth in negative scope', {
      rule: 'refSpawn',
      region: nested,
      defId: 'truthReification',
      sig: expectedSig,
    })
    const nestedRef = onlyNewNode(nestedStart, nestedRecorder.diagram, nested)
    const nestedWitness = onlyNewWire(
      nestedStart,
      nestedRecorder.diagram,
      nested,
    )
    expect(nestedRecorder.diagram.nodes[nestedRef]).toMatchObject({
      kind: 'ref',
      region: nested,
    })
    expect(nestedRecorder.diagram.wires[nestedWitness]!.scope).toBe(nested)
  })
})

describe('thin primitive recording and deterministic delta lookup', () => {
  it('applies and records exactly one existing ProofStep per call', () => {
    const builder = new DiagramBuilder()
    const cut = builder.cut(builder.root)
    const relation = builder.relWire(builder.root, relSig([]))
    const before = builder.build()
    const recorder = new PrimitiveStepRecorder(
      before,
      verifyTheory(buildFregeTheory()),
    )
    const step: ProofStep = { rule: 'atomSpawn', region: cut, wire: relation }

    recorder.record('spawn one nullary atom', step)

    expect(recorder.actions).toEqual([{
      label: 'spawn one nullary atom',
      steps: [step],
      placements: [],
    }])
    expect(onlyNewNode(before, recorder.diagram, cut)).toBe('n')
    expect(() => onlyNewNode(recorder.diagram, recorder.diagram, cut))
      .toThrowError(/expected exactly one new node.*found 0/i)
  })

  it('cardinality-checks new wires and cuts instead of selecting the first match', () => {
    const builder = new DiagramBuilder()
    const cut = builder.cut(builder.root)
    const before = builder.build()
    const recorder = new PrimitiveStepRecorder(
      before,
      verifyTheory(buildFregeTheory()),
    )
    recorder.record('introduce one individual', {
      rule: 'vacuousIntro',
      scope: cut,
      sig: IOTA,
    })
    expect(onlyNewWire(before, recorder.diagram, cut)).toBe('r1_vac')

    const beforeCuts = recorder.diagram
    recorder.record('introduce a double cut', {
      rule: 'doubleCutIntro',
      sel: {
        region: cut,
        regions: [],
        nodes: [],
        wires: [],
      },
    })
    const outer = onlyNewCut(beforeCuts, recorder.diagram, cut)
    expect(onlyNewCut(beforeCuts, recorder.diagram, outer)).toMatch(/^dc/)
    expect(() => onlyNewCut(beforeCuts, recorder.diagram))
      .toThrowError(/expected exactly one new cut.*found 2/i)
  })
})

describe('theory surface exclusions', () => {
  it('exports no composite proof surface and carries no displaced vocabulary', async () => {
    const barrel = await import('../../src/theories')
    expect(Object.keys(barrel).sort()).toEqual([
      'buildFregeTheory',
      'natRelation',
    ])

    const directory = fileURLToPath(new URL('../../src/theories', import.meta.url))
    const source = readdirSync(directory)
      .filter((name) => name.endsWith('.ts'))
      .map((name) => readFileSync(`${directory}/${name}`, 'utf8'))
      .join('\n')
    const prohibited = [
      'compre' + 'hension',
      'exten' + 'sional',
      "kind: 'te" + "rm'",
      "kind: 'bo" + "dy'",
      'beta' + 'Eta',
      'instan' + 'tiate',
      'macro',
      'tactic',
      'composeActions',
      'replayProof',
    ]
    for (const term of prohibited) expect(source).not.toContain(term)
  })
})
