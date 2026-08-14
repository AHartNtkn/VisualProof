import { describe, expect, it } from 'vitest'
import { sameDiagram } from '../../src/kernel/diagram/canonical/iso'
import type {
  Diagram,
  NodeId,
  RegionId,
  WireId,
} from '../../src/kernel/diagram/diagram'
import { IOTA, relSig } from '../../src/kernel/diagram/sig'
import { verifyTheory } from '../../src/kernel/proof/context'
import {
  theoremFromJson,
  theoremToJson,
} from '../../src/kernel/proof/json'
import { checkTheorem, type Theorem } from '../../src/kernel/proof/theorem'
import {
  atom,
  biconditional,
  declareWire,
  emptyGraph,
  finishDiagramWithBoundary,
  quantifierScope,
} from '../../src/theories/graph'
import {
  PrimitiveStepRecorder,
  onlyNewCut,
  onlyNewNode,
  onlyNewWire,
} from '../../src/theories/record'
import {
  associativityInductionReification,
  relationIdentityReification,
  truthReification,
  explicitMaterialOf,
} from '../../src/theories/reification'
import { bareWireAssembly } from '../../src/kernel/rules/identity-rules'

const UNARY = relSig([IOTA])

function directCuts(
  diagram: Diagram,
  parent: RegionId,
): readonly RegionId[] {
  return Object.entries(diagram.regions)
    .filter(([, region]) =>
      region.kind === 'cut' && region.parent === parent)
    .map(([id]) => id)
}

function directNodes(
  diagram: Diagram,
  region: RegionId,
): readonly NodeId[] {
  return Object.entries(diagram.nodes)
    .filter(([, node]) => node.region === region)
    .map(([id]) => id)
}

function exactOne<T>(values: readonly T[], what: string): T {
  expect(values, what).toHaveLength(1)
  return values[0]!
}

function endpointWire(
  diagram: Diagram,
  node: NodeId,
  kind: 'head' | 'arg',
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
            endpoint.port.kind === 'arg'
            && endpoint.port.index === index
          )
        )))
      .map(([id]) => id),
    `${kind} wire for '${node}'`,
  )
}

function expectedConjunctionClosure() {
  let graph = emptyGraph()
  const relations = quantifierScope(
    graph,
    graph.root,
    'forall',
    [UNARY, UNARY],
  )
  graph = relations.graph
  const [r, s] = relations.value.variables
  const witness = declareWire(graph, relations.value.body, UNARY)
  graph = witness.graph
  const individuals = quantifierScope(
    graph,
    relations.value.body,
    'forall',
    [IOTA],
  )
  graph = individuals.graph
  const x = individuals.value.variables[0]!
  const iff = biconditional(graph, individuals.value.body)
  graph = iff.graph
  graph = atom(
    graph,
    iff.value.forward.antecedent,
    witness.value,
    [x],
  ).graph
  graph = atom(graph, iff.value.forward.consequent, r!, [x]).graph
  graph = atom(graph, iff.value.forward.consequent, s!, [x]).graph
  graph = atom(graph, iff.value.reverse.antecedent, r!, [x]).graph
  graph = atom(graph, iff.value.reverse.antecedent, s!, [x]).graph
  graph = atom(
    graph,
    iff.value.reverse.consequent,
    witness.value,
    [x],
  ).graph
  return finishDiagramWithBoundary(graph, [])
}

/**
 * Independent construction-level regression for
 *   forall R,S. exists Q. forall x. Q(x) <-> (R(x) and S(x)).
 *
 * It deliberately uses the same strongest-form ownership model as production:
 * build one explicit two-node G in a negative branch, iterate exact copies,
 * then let one relation sever create the shared witness.
 */
function conjunctionClosureTheorem(): Theorem {
  const blank = emptyGraph()
  const lhs = finishDiagramWithBoundary(blank, [])
  const context = verifyTheory({ relations: [], theorems: [] })
  const recorder = new PrimitiveStepRecorder(lhs, context)

  let before = recorder.diagram
  recorder.record('open the universal relation scope', {
    rule: 'doubleCutIntro',
    sel: {
      region: recorder.diagram.root,
      regions: [],
      nodes: [],
      wires: [],
    },
  })
  const relationScope = onlyNewCut(
    before,
    recorder.diagram,
    recorder.diagram.root,
  )
  const relationBody = exactOne(
    directCuts(recorder.diagram, relationScope),
    'positive relation body',
  )

  before = recorder.diagram
  recorder.record('introduce universally scoped R', {
    rule: 'vacuity',
    direction: 'insert',
    assembly: bareWireAssembly('R', relationScope, UNARY),
  })
  const r = onlyNewWire(before, recorder.diagram, relationScope)
  before = recorder.diagram
  recorder.record('introduce universally scoped S', {
    rule: 'vacuity',
    direction: 'insert',
    assembly: bareWireAssembly('S', relationScope, UNARY),
  })
  const s = onlyNewWire(before, recorder.diagram, relationScope)

  before = recorder.diagram
  recorder.record('open the universal individual scope', {
    rule: 'doubleCutIntro',
    sel: {
      region: relationBody,
      regions: [],
      nodes: [],
      wires: [],
    },
  })
  const individualScope = onlyNewCut(before, recorder.diagram, relationBody)
  const individualBody = exactOne(
    directCuts(recorder.diagram, individualScope),
    'positive individual body',
  )
  before = recorder.diagram
  recorder.record('introduce universally scoped x', {
    rule: 'vacuity',
    direction: 'insert',
    assembly: bareWireAssembly('x', individualScope, IOTA),
  })
  const x = onlyNewWire(before, recorder.diagram, individualScope)

  before = recorder.diagram
  recorder.record('open the first implication', {
    rule: 'doubleCutIntro',
    sel: {
      region: individualBody,
      regions: [],
      nodes: [],
      wires: [],
    },
  })
  const forward = onlyNewCut(before, recorder.diagram, individualBody)
  const forwardConsequent = exactOne(
    directCuts(recorder.diagram, forward),
    'forward consequent',
  )

  const sourceNodes: NodeId[] = []
  for (const [name, relation] of [['R', r], ['S', s]] as const) {
    before = recorder.diagram
    recorder.record(`insert ${name}(x) in the negative source`, {
      rule: 'atomSpawn',
      region: forward,
      wire: relation,
    })
    const node = onlyNewNode(before, recorder.diagram, forward)
    const localArgument = onlyNewWire(before, recorder.diagram, forward)
    recorder.record(`identify ${name}'s local argument with x`, {
      rule: 'wireJoin',
      input: {
        a: x,
        b: localArgument,
      },
    })
    expect(endpointWire(recorder.diagram, node, 'arg', 0)).toBe(x)
    sourceNodes.push(node)
  }

  before = recorder.diagram
  recorder.record('iterate the exact conjunction into the consequent', {
    rule: 'iteration',
    sel: {
      region: forward,
      regions: [],
      nodes: sourceNodes,
      wires: [],
    },
    target: forwardConsequent,
  })
  expect(directNodes(recorder.diagram, forwardConsequent)
    .filter((node) => before.nodes[node] === undefined)).toHaveLength(2)

  before = recorder.diagram
  recorder.record('iterate the complete implication as its reverse twin', {
    rule: 'iteration',
    sel: {
      region: individualBody,
      regions: [forward],
      nodes: [],
      wires: [],
    },
    target: individualBody,
  })
  const reverse = onlyNewCut(before, recorder.diagram, individualBody)
  const reverseConsequent = exactOne(
    directCuts(recorder.diagram, reverse),
    'reverse consequent',
  )
  const reverseWitnessMaterial = directNodes(
    recorder.diagram,
    reverseConsequent,
  )
  expect(reverseWitnessMaterial).toHaveLength(2)

  recorder.recordRelationSever('abstract one exact copy in each implication', {
    scope: relationBody,
    occurrences: [
      {
        sel: {
          region: forward,
          regions: [],
          nodes: sourceNodes,
          wires: [],
        },
        args: [x],
      },
      {
        sel: {
          region: reverseConsequent,
          regions: [],
          nodes: reverseWitnessMaterial,
          wires: [],
        },
        args: [x],
      },
    ],
  })

  return {
    name: 'conjunctionRelationReification',
    lhs,
    rhs: expectedConjunctionClosure(),
    actions: recorder.actions,
  }
}

describe('strongest-form relation reification construction', () => {
  it('records the closed relation-identity theorem', () => {
    const theorem = relationIdentityReification()
    expect(theorem.name).toBe('relationIdentityReification')
    expect(theorem.lhs.boundary).toEqual([])
    expect(theorem.rhs.boundary).toEqual([])
    expect(() => checkTheorem(
      theorem,
      verifyTheory({ relations: [], theorems: [] }),
    )).not.toThrow()
  })

  it('abstracts a genuine two-node conjunction rather than a special atom', () => {
    const theorem = conjunctionClosureTheorem()
    const context = verifyTheory({ relations: [], theorems: [] })
    const blank = finishDiagramWithBoundary(emptyGraph(), [])
    expect(sameDiagram(
      theorem.lhs.diagram, blank.diagram,
      theorem.lhs.boundary, blank.boundary,
    )).toBe(true)
    expect(() => checkTheorem(theorem, context)).not.toThrow()
    const severActions = theorem.actions.filter((action) =>
      action.steps.some((step) =>
        (step.rule === 'wireSever' && step.input.scope !== undefined)
        || step.rule === 'abstractFormal'
        || step.rule === 'identityAbstract'
        || step.rule === 'endsSpawn'))
    expect(severActions).toHaveLength(1)

    const restored = theoremFromJson(JSON.parse(JSON.stringify(
      theoremToJson(theorem),
    )))
    expect(() => checkTheorem(restored, context)).not.toThrow()
    expect(() => checkTheorem({
      ...theorem,
      actions: theorem.actions.filter((action) =>
        action !== severActions[0]),
    }, context)).toThrowError(
      /proof does not arrive at the stated right-hand side|failed/i,
    )
  })

  it('uses two distinct branch regions for blank truth occurrences', () => {
    const theorem = truthReification()
    const spawn = exactOne(
      theorem.actions.flatMap((action) => action.steps)
        .filter((step) => step.rule === 'endsSpawn'),
      'truth witness ends spawn',
    )
    if (spawn.rule !== 'endsSpawn') throw new Error('unreachable truth spawn')
    expect(spawn.sites).toHaveLength(2)
    expect(spawn.sites[0]!.region).not.toBe(spawn.sites[1]!.region)
    expect(spawn.sites.every((site) => site.args.length === 0)).toBe(true)
  })

  it('embeds arbitrary nested carrier material in grounding actions, not definitions', () => {
    const theorem = associativityInductionReification()
    const material = explicitMaterialOf(theorem)
    expect(Object.keys(material.diagram.nodes).length).toBeGreaterThan(1)
    expect(Object.keys(material.diagram.regions).length).toBeGreaterThan(1)
    expect(Object.values(material.diagram.nodes)
      .every((node) => node.kind !== 'ref')).toBe(true)
    const rules = new Set(theorem.actions.flatMap((action) =>
      action.steps.map((step) => step.rule)))
    expect(rules.has('refLeaf')).toBe(false)
    expect(rules.has('refSpawn')).toBe(false)
    expect(rules.has('unfold')).toBe(false)
    expect(rules.has('fold')).toBe(false)
  })
})
