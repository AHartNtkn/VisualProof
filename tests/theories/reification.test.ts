import { readFileSync, readdirSync } from 'node:fs'
import { fileURLToPath } from 'node:url'
import { describe, expect, it } from 'vitest'
import type { DiagramWithBoundary } from '../../src/kernel/diagram/boundary'
import { exploreForm } from '../../src/kernel/diagram/canonical/explore'
import type {
  Diagram,
  NodeId,
  RegionId,
  WireId,
} from '../../src/kernel/diagram/diagram'
import { polarity } from '../../src/kernel/diagram/regions'
import { IOTA, relSig, sigKey, type Sig } from '../../src/kernel/diagram/sig'
import {
  registerTheorem,
  verifyTheory,
} from '../../src/kernel/proof/context'
import { applyActionWithReceipt } from '../../src/kernel/proof/action'
import {
  theoremFromJson,
  theoremToJson,
} from '../../src/kernel/proof/json'
import {
  checkTheorem,
  type Theorem,
} from '../../src/kernel/proof/theorem'
import {
  atom,
  biconditional,
  declareWire,
  emptyGraph,
  finishDiagramWithBoundary,
  identity,
  implication,
  quantifierScope,
  type GraphConstruction,
} from '../../src/theories/graph'
import { buildFregeTheory } from '../../src/theories'
import {
  associativityInductionReification,
  commutativityInductionReification,
  relationIdentityReification,
  rightIdentityInductionReification,
  successorShiftInductionReification,
  truthReification,
} from '../../src/theories/reification'

const UNARY = relSig([IOTA])
const BINARY = relSig([IOTA, IOTA])
const TERNARY = relSig([IOTA, IOTA, IOTA])

function exactlyOne<T>(values: readonly T[], what: string): T {
  expect(values, what).toHaveLength(1)
  return values[0]!
}

function endpointWire(
  diagram: Diagram,
  node: NodeId,
  kind: 'head' | 'arg',
  index?: number,
): WireId {
  return exactlyOne(
    Object.entries(diagram.wires)
      .filter(([, wire]) => wire.endpoints.some((endpoint) =>
        endpoint.node === node
        && endpoint.port.kind === kind
        && (
          kind === 'head'
          || (
            endpoint.port.kind === 'arg'
            && endpoint.port.index === index
          )
        )))
      .map(([id]) => id),
    `one ${kind} wire for '${node}'`,
  )
}

function captureOnly(signatures: readonly Sig[]): DiagramWithBoundary {
  let graph = emptyGraph()
  const boundary: WireId[] = []
  for (const signature of signatures) {
    const capture = declareWire(graph, graph.root, signature)
    graph = capture.graph
    boundary.push(capture.value)
  }
  return finishDiagramWithBoundary(graph, boundary)
}

type UnaryMaterial = (
  graph: GraphConstruction,
  region: RegionId,
  variable: WireId,
  captures: readonly WireId[],
) => GraphConstruction

function unaryReificationFigure(
  captureSignatures: readonly Sig[],
  drawMaterial: UnaryMaterial,
): DiagramWithBoundary {
  let graph = emptyGraph()
  const captures: WireId[] = []
  for (const signature of captureSignatures) {
    const capture = declareWire(graph, graph.root, signature)
    graph = capture.graph
    captures.push(capture.value)
  }
  const witness = declareWire(graph, graph.root, UNARY)
  graph = witness.graph
  const universal = quantifierScope(graph, graph.root, 'forall', [IOTA])
  graph = universal.graph
  const variable = universal.value.variables[0]!
  const iff = biconditional(graph, universal.value.body)
  graph = iff.graph
  graph = atom(
    graph,
    iff.value.forward.antecedent,
    witness.value,
    [variable],
  ).graph
  graph = drawMaterial(
    graph,
    iff.value.forward.consequent,
    variable,
    captures,
  )
  graph = drawMaterial(
    graph,
    iff.value.reverse.antecedent,
    variable,
    captures,
  )
  graph = atom(
    graph,
    iff.value.reverse.consequent,
    witness.value,
    [variable],
  ).graph
  return finishDiagramWithBoundary(graph, captures)
}

function relationIdentityFigure(): DiagramWithBoundary {
  let graph = emptyGraph()
  const relationUniversal = quantifierScope(
    graph,
    graph.root,
    'forall',
    [UNARY],
  )
  graph = relationUniversal.graph
  const source = relationUniversal.value.variables[0]!
  const witness = declareWire(
    graph,
    relationUniversal.value.body,
    UNARY,
  )
  graph = witness.graph
  const individualUniversal = quantifierScope(
    graph,
    relationUniversal.value.body,
    'forall',
    [IOTA],
  )
  graph = individualUniversal.graph
  const variable = individualUniversal.value.variables[0]!
  const iff = biconditional(graph, individualUniversal.value.body)
  graph = iff.graph
  for (const [region, relation] of [
    [iff.value.forward.antecedent, witness.value],
    [iff.value.forward.consequent, source],
    [iff.value.reverse.antecedent, source],
    [iff.value.reverse.consequent, witness.value],
  ] as const) {
    graph = atom(graph, region, relation, [variable]).graph
  }
  return finishDiagramWithBoundary(graph, [])
}

function truthFigure(): DiagramWithBoundary {
  let graph = emptyGraph()
  const witness = declareWire(graph, graph.root, relSig([]))
  graph = witness.graph
  const iff = biconditional(graph, graph.root)
  graph = iff.graph
  graph = atom(
    graph,
    iff.value.forward.antecedent,
    witness.value,
    [],
  ).graph
  graph = atom(
    graph,
    iff.value.reverse.consequent,
    witness.value,
    [],
  ).graph
  return finishDiagramWithBoundary(graph, [])
}

function rightIdentityMaterial(
  initial: GraphConstruction,
  region: RegionId,
  inductionVariable: WireId,
  captures: readonly WireId[],
): GraphConstruction {
  const [zero, plus] = captures
  const quantified = quantifierScope(initial, region, 'forall', [IOTA, IOTA])
  const [zeroValue, output] = quantified.value.variables
  const claim = implication(quantified.graph, quantified.value.body)
  let graph = claim.graph
  graph = atom(
    graph,
    claim.value.antecedent,
    zero!,
    [zeroValue!],
  ).graph
  graph = atom(
    graph,
    claim.value.antecedent,
    plus!,
    [inductionVariable, zeroValue!, output!],
  ).graph
  return identity(
    graph,
    claim.value.consequent,
    [output!, inductionVariable],
  ).graph
}

function associativityMaterial(
  initial: GraphConstruction,
  region: RegionId,
  inductionVariable: WireId,
  captures: readonly WireId[],
): GraphConstruction {
  const plus = captures[0]!
  const quantified = quantifierScope(
    initial,
    region,
    'forall',
    [IOTA, IOTA, IOTA, IOTA, IOTA],
  )
  const [right, third, firstSum, output, innerSum] =
    quantified.value.variables
  const claim = implication(quantified.graph, quantified.value.body)
  let graph = claim.graph
  graph = atom(
    graph,
    claim.value.antecedent,
    plus,
    [inductionVariable, right!, firstSum!],
  ).graph
  graph = atom(
    graph,
    claim.value.antecedent,
    plus,
    [firstSum!, third!, output!],
  ).graph
  graph = atom(
    graph,
    claim.value.antecedent,
    plus,
    [right!, third!, innerSum!],
  ).graph
  return atom(
    graph,
    claim.value.consequent,
    plus,
    [inductionVariable, innerSum!, output!],
  ).graph
}

function successorShiftMaterial(
  initial: GraphConstruction,
  region: RegionId,
  inductionVariable: WireId,
  captures: readonly WireId[],
): GraphConstruction {
  const [successor, plus] = captures
  const quantified = quantifierScope(
    initial,
    region,
    'forall',
    [IOTA, IOTA, IOTA, IOTA],
  )
  const [right, rightSuccessor, output, outputSuccessor] =
    quantified.value.variables
  const claim = implication(quantified.graph, quantified.value.body)
  let graph = claim.graph
  graph = atom(
    graph,
    claim.value.antecedent,
    successor!,
    [right!, rightSuccessor!],
  ).graph
  graph = atom(
    graph,
    claim.value.antecedent,
    plus!,
    [inductionVariable, right!, output!],
  ).graph
  graph = atom(
    graph,
    claim.value.antecedent,
    successor!,
    [output!, outputSuccessor!],
  ).graph
  return atom(
    graph,
    claim.value.consequent,
    plus!,
    [inductionVariable, rightSuccessor!, outputSuccessor!],
  ).graph
}

function commutativityMaterial(
  initial: GraphConstruction,
  region: RegionId,
  inductionVariable: WireId,
  captures: readonly WireId[],
): GraphConstruction {
  const plus = captures[0]!
  const quantified = quantifierScope(initial, region, 'forall', [IOTA, IOTA])
  const [right, output] = quantified.value.variables
  const claim = implication(quantified.graph, quantified.value.body)
  let graph = claim.graph
  graph = atom(
    graph,
    claim.value.antecedent,
    plus,
    [inductionVariable, right!, output!],
  ).graph
  return atom(
    graph,
    claim.value.consequent,
    plus,
    [right!, inductionVariable, output!],
  ).graph
}

type ReificationCase = {
  readonly name: string
  readonly make: () => Theorem
  readonly captureSignatures: readonly Sig[]
  readonly rhs: () => DiagramWithBoundary
}

const reificationCases: readonly ReificationCase[] = [
  {
    name: 'relationIdentityReification',
    make: relationIdentityReification,
    captureSignatures: [],
    rhs: relationIdentityFigure,
  },
  {
    name: 'truthReification',
    make: truthReification,
    captureSignatures: [],
    rhs: truthFigure,
  },
  {
    name: 'rightIdentityInductionReification',
    make: rightIdentityInductionReification,
    captureSignatures: [UNARY, TERNARY],
    rhs: () => unaryReificationFigure(
      [UNARY, TERNARY],
      rightIdentityMaterial,
    ),
  },
  {
    name: 'associativityInductionReification',
    make: associativityInductionReification,
    captureSignatures: [TERNARY],
    rhs: () => unaryReificationFigure(
      [TERNARY],
      associativityMaterial,
    ),
  },
  {
    name: 'successorShiftInductionReification',
    make: successorShiftInductionReification,
    captureSignatures: [BINARY, TERNARY],
    rhs: () => unaryReificationFigure(
      [BINARY, TERNARY],
      successorShiftMaterial,
    ),
  },
  {
    name: 'commutativityInductionReification',
    make: commutativityInductionReification,
    captureSignatures: [TERNARY],
    rhs: () => unaryReificationFigure(
      [TERNARY],
      commutativityMaterial,
    ),
  },
]

function flattenedRules(theorem: Theorem): readonly string[] {
  return theorem.actions.flatMap((action) =>
    action.steps.map((step) => step.rule))
}

function theoremByName(
  theorems: readonly Theorem[],
  name: string,
): Theorem {
  return exactlyOne(
    theorems.filter((theorem) => theorem.name === name),
    `theorem '${name}'`,
  )
}

describe('recorded general relation reification', () => {
  it('records the exact closed identity, blank truth, and captured carrier statements', () => {
    for (const testCase of reificationCases) {
      const theorem = testCase.make()
      const expectedLhs = captureOnly(testCase.captureSignatures)
      const expectedRhs = testCase.rhs()

      expect(theorem.name).toBe(testCase.name)
      expect(exploreForm(theorem.lhs.diagram, theorem.lhs.boundary))
        .toBe(exploreForm(expectedLhs.diagram, expectedLhs.boundary))
      expect(exploreForm(theorem.rhs.diagram, theorem.rhs.boundary))
        .toBe(exploreForm(expectedRhs.diagram, expectedRhs.boundary))
      expect(theorem.lhs.boundary.map((wire) =>
        sigKey(theorem.lhs.diagram.wires[wire]!.sig)))
        .toEqual(testCase.captureSignatures.map(sigKey))
      expect(theorem.rhs.boundary.map((wire) =>
        sigKey(theorem.rhs.diagram.wires[wire]!.sig)))
        .toEqual(testCase.captureSignatures.map(sigKey))
    }
  })

  it('replays every reification without definitions, refs, or privileged spawn', () => {
    const context = verifyTheory({ relations: [], theorems: [] })
    for (const testCase of reificationCases) {
      const theorem = testCase.make()
      expect(() => checkTheorem(theorem, context)).not.toThrow()
      expect(flattenedRules(theorem)).not.toContain('refSpawn')
      expect(flattenedRules(theorem)).not.toContain('unfold')
      expect(flattenedRules(theorem)).not.toContain('fold')
      expect([
        ...Object.values(theorem.lhs.diagram.nodes),
        ...Object.values(theorem.rhs.diagram.nodes),
      ].every((node) => node.kind !== 'ref')).toBe(true)
      expect(theorem.actions.every((action) =>
        action.steps.length === 1)).toBe(true)
    }
  })

  it('gets each fresh witness from its one strongest-form sever', () => {
    const context = verifyTheory({ relations: [], theorems: [] })
    for (const testCase of reificationCases) {
      const theorem = testCase.make()
      let diagram = theorem.lhs.diagram
      const severWires: WireId[] = []

      for (const action of theorem.actions) {
        const receipt = applyActionWithReceipt(diagram, action, context)
        const step = action.steps[0]!
        if (step.rule === 'wireSever' && step.input.kind === 'relation') {
          const created = receipt.allocation.wires.filter((wire) =>
            receipt.result.wires[wire]?.sig.kind === 'rel')
          expect(created).toHaveLength(1)
          severWires.push(created[0]!)
        }
        diagram = receipt.result
      }

      const witness = exactlyOne(severWires, `${theorem.name} sever witness`)
      expect(diagram.wires[witness]).toBeDefined()
      expect(diagram.wires[witness]!.endpoints).toHaveLength(2)
      expect(diagram.wires[witness]!.endpoints.every((endpoint) =>
        endpoint.port.kind === 'head'
        && diagram.nodes[endpoint.node]?.kind === 'atom')).toBe(true)
      expect(theorem.lhs.boundary).not.toContain(witness)
      expect(theorem.rhs.boundary).not.toContain(witness)
    }
  })

  it('makes the sever action indispensable in every reification proof', () => {
    const context = verifyTheory({ relations: [], theorems: [] })
    for (const testCase of reificationCases) {
      const theorem = testCase.make()
      const severIndexes = theorem.actions
        .map((action, index) =>
          action.steps[0]?.rule === 'wireSever' ? index : -1)
        .filter((index) => index >= 0)
      expect(severIndexes).toHaveLength(1)
      for (const severIndex of severIndexes) {
        expect(() => checkTheorem({
          ...theorem,
          actions: theorem.actions.filter((_, index) => index !== severIndex),
        }, context)).toThrowError(
          /proof does not arrive at the stated right-hand side/i,
        )
      }
    }
  })

  it('round-trips every standalone reification theorem and re-verifies it', () => {
    const context = verifyTheory({ relations: [], theorems: [] })
    for (const testCase of reificationCases) {
      const restored = theoremFromJson(JSON.parse(JSON.stringify(
        theoremToJson(testCase.make()),
      )))
      expect(() => checkTheorem(restored, context)).not.toThrow()
    }
  })
})

describe('logical dependency prefix', () => {
  it('registers only ordinary relations and the exact ordered theorem prefix', () => {
    const theory = buildFregeTheory()
    expect(theory.relations.map(([name]) => name)).toEqual(['nat'])
    expect(theory.theorems.map((theorem) => theorem.name)).toEqual([
      'ordinaryEqualityContradiction',
      'relationIdentityReification',
      'truthReification',
      'rightIdentityInductionReification',
      'associativityInductionReification',
      'successorShiftInductionReification',
      'commutativityInductionReification',
      'existsProp',
    ])
    expect(() => verifyTheory(theory)).not.toThrow()
  })

  it('round-trips and verifies every theorem against exactly its prior prefix', () => {
    const theory = buildFregeTheory()
    let prefix = verifyTheory({
      relations: theory.relations,
      theorems: [],
    })
    for (const theorem of theory.theorems) {
      const restored = theoremFromJson(JSON.parse(JSON.stringify(
        theoremToJson(theorem),
      )))
      expect(() => checkTheorem(restored, prefix)).not.toThrow()
      prefix = registerTheorem(prefix, restored)
    }
  })

  it('derives existsProp from blank by citing sever-derived truth', () => {
    const theory = buildFregeTheory()
    const exists = theoremByName(theory.theorems, 'existsProp')
    expect(exists.lhs.boundary).toEqual([])
    expect(exists.rhs.boundary).toEqual([])
    expect(flattenedRules(exists)).toEqual([
      'theorem',
      'erasure',
      'doubleCutElim',
    ])
    expect(exists.actions[0]!.steps[0]).toMatchObject({
      rule: 'theorem',
      name: 'truthReification',
      direction: 'forward',
      at: {
        sel: {
          region: exists.lhs.diagram.root,
          regions: [],
          nodes: [],
          wires: [],
        },
        args: [],
      },
    })

    let context = verifyTheory({
      relations: theory.relations,
      theorems: [],
    })
    for (const theorem of theory.theorems) {
      if (theorem.name === 'existsProp') break
      context = registerTheorem(context, theorem)
    }

    let diagram = exists.lhs.diagram
    const cited = applyActionWithReceipt(
      diagram,
      exists.actions[0]!,
      context,
    )
    const citedWitness = exactlyOne(
      cited.allocation.wires.filter((wire) =>
        cited.result.wires[wire]?.sig.kind === 'rel'),
      'truth-citation witness',
    )
    diagram = cited.result
    for (const action of exists.actions.slice(1)) {
      diagram = applyActionWithReceipt(diagram, action, context).result
    }

    expect(Object.values(diagram.regions)).toEqual([{ kind: 'sheet' }])
    const finalAtom = exactlyOne(
      Object.entries(diagram.nodes),
      'one final proposition atom',
    )
    expect(finalAtom[1]).toMatchObject({
      kind: 'atom',
      region: diagram.root,
      sig: relSig([]),
    })
    expect(endpointWire(diagram, finalAtom[0], 'head')).toBe(citedWitness)
    expect(diagram.wires[citedWitness]).toMatchObject({
      scope: diagram.root,
      sig: relSig([]),
    })
    expect(() => checkTheorem(exists, context)).not.toThrow()
  })

  it('requires both the truth citation and its ordinary cleanup', () => {
    const theory = buildFregeTheory()
    const exists = theoremByName(theory.theorems, 'existsProp')
    let context = verifyTheory({
      relations: theory.relations,
      theorems: [],
    })
    for (const theorem of theory.theorems) {
      if (theorem.name === 'existsProp') break
      context = registerTheorem(context, theorem)
    }
    exists.actions.forEach((_, removed) => {
      expect(() => checkTheorem({
        ...exists,
        actions: exists.actions.filter((__, index) => index !== removed),
      }, context)).toThrow()
    })
  })
})

describe('theory surface exclusions', () => {
  it('exports no composite proof API and contains no displaced authority', async () => {
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
      'refSpawn',
      'isExactReificationDefinition',
      'exact reification definition',
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
      ['identity', 'Contradiction'].join(''),
    ]
    for (const term of prohibited) expect(source).not.toContain(term)
  })

  it('keeps every theorem boundary root-scoped and ordered', () => {
    for (const theorem of buildFregeTheory().theorems) {
      for (const side of [theorem.lhs, theorem.rhs]) {
        expect(side.boundary.every((wire) =>
          side.diagram.wires[wire]!.scope === side.diagram.root)).toBe(true)
      }
    }
  })

  it('keeps sever witnesses existential rather than universally scoped', () => {
    const context = verifyTheory({ relations: [], theorems: [] })
    for (const testCase of reificationCases) {
      const theorem = testCase.make()
      let diagram = theorem.lhs.diagram
      let severCount = 0
      for (const action of theorem.actions) {
        const step = action.steps[0]!
        if (step.rule === 'wireSever' && step.input.kind === 'relation') {
          severCount += 1
          expect(polarity(diagram, step.input.scope)).toBe('positive')
        }
        diagram = applyActionWithReceipt(diagram, action, context).result
      }
      expect(severCount).toBe(1)
    }
  })
})
