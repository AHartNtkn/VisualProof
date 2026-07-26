import { readFileSync, readdirSync } from 'node:fs'
import { fileURLToPath } from 'node:url'
import { describe, expect, it } from 'vitest'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { exploreForm } from '../../src/kernel/diagram/canonical/explore'
import { dwbToJson } from '../../src/kernel/diagram/json'
import { IOTA, relSig, sigKey } from '../../src/kernel/diagram/sig'
import { verifyTheory } from '../../src/kernel/proof/context'
import type { ProofStep } from '../../src/kernel/proof/step'
import {
  atom,
  biconditional,
  declareWire,
  emptyGraph,
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
  })

  it('keeps each handwritten induction witness first and only real captures after it', () => {
    const definitions = [
      [rightIdentityInductionReification(), ['(i)', '(i)', '(i,i,i)']],
      [associativityInductionReification(), ['(i)', '(i,i,i)']],
      [successorShiftInductionReification(), ['(i)', '(i,i)', '(i,i,i)']],
      [commutativityInductionReification(), ['(i)', '(i,i,i)']],
    ] as const

    for (const [definition, signatures] of definitions) {
      expect(definition.boundary.map((wire) =>
        sigKey(definition.diagram.wires[wire]!.sig)))
        .toEqual(signatures)
      expect(witnessAtoms(definition)).toHaveLength(2)
      expect(definition.boundary.every((wire) =>
        definition.diagram.wires[wire]!.scope === definition.diagram.root
        && definition.diagram.wires[wire]!.endpoints.length > 0))
        .toBe(true)
    }
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
