import { IOTA, relSig } from '../kernel/diagram/sig'
import type {
  NodeId,
  RegionId,
  WireId,
} from '../kernel/diagram/diagram'
import { findDeiterationEvidence } from '../kernel/rules/iteration'
import {
  registerTheorem,
  verifyTheory,
  type ProofContext,
  type Theory,
} from '../kernel/proof/context'
import { bareWireAssembly } from '../kernel/rules/identity-rules'
import type { Theorem } from '../kernel/proof/theorem'
import {
  BINARY,
  TERNARY,
  UNARY,
  directCuts,
  directNodes,
  endpointWire,
  exactOne,
  relationApplicationContent,
  relationWire,
  rightIdentityCarrierContent,
  scopedWires,
} from './arithmetic-support'
import {
  atom,
  declareWire,
  emptyGraph,
  finishDiagramWithBoundary,
  identity,
  implication,
  quantifierScope,
} from './graph'
import {
  PrimitiveStepRecorder,
  onlyNewCut,
  onlyNewNode,
  onlyNewWire,
} from './record'
import {
  rightIdentityCarrierInductive,
} from './arithmetic-right-carrier'
import type { ArithmeticStatements } from './statements'

function plusSingleValuedContent() {
  let graph = emptyGraph()
  const plus = declareWire(graph, graph.root, TERNARY)
  graph = plus.graph
  const variables = quantifierScope(
    graph,
    graph.root,
    'forall',
    [IOTA, IOTA, IOTA, IOTA],
  )
  graph = variables.graph
  const [left, right, first, second] = variables.value.variables
  const claim = implication(graph, variables.value.body)
  graph = claim.graph
  graph = atom(
    graph,
    claim.value.antecedent,
    plus.value,
    [left!, right!, first!],
  ).graph
  graph = atom(
    graph,
    claim.value.antecedent,
    plus.value,
    [left!, right!, second!],
  ).graph
  graph = identity(
    graph,
    claim.value.consequent,
    [first!, second!],
  ).graph
  return finishDiagramWithBoundary(graph, [plus.value])
}

function deiterateNode(
  recorder: PrimitiveStepRecorder,
  label: string,
  region: RegionId,
  node: NodeId,
): void {
  const sel = {
    region,
    regions: [],
    nodes: [node],
    wires: [],
  } as const
  const evidence = findDeiterationEvidence(
    recorder.diagram,
    sel,
  )
  recorder.record(label, {
    rule: 'deiteration',
    sel,
    justifier: evidence.justifier,
    certificate: evidence.certificate,
  })
}

/**
 * The forward half starts by citing the closed carrier-support theorem and
 * reuses its quantified primitive shell and standing hypotheses. Its exact
 * Base(E) and Closure(E) facts are copied into the negative claim antecedent,
 * where the backward half uses them to discharge the directly grounded Nat
 * carrier. The two halves meet before closing the claim, with both the source
 * and derived addition facts plus their witnessed equality still recorded.
 */
function plusRightUnit(
  statements: ArithmeticStatements,
  context: ProofContext,
): Theorem {
  const lhs = finishDiagramWithBoundary(emptyGraph(), [])
  const forward = new PrimitiveStepRecorder(lhs, context)

  forward.record('seed right-unit shell from direct carrier support', {
    rule: 'theorem',
    name: 'rightIdentityCarrierInductive',
    direction: 'forward',
    at: {
      sel: {
        region: forward.diagram.root,
        regions: [],
        nodes: [],
        wires: [],
      },
      args: [],
    },
  })
  const forwardPrimitiveScope = exactOne(
    directCuts(forward.diagram, forward.diagram.root),
    'forward primitive scope',
  )
  const forwardPrimitiveBody = exactOne(
    directCuts(forward.diagram, forwardPrimitiveScope),
    'forward primitive body',
  )
  const forwardHypotheses = exactOne(
    directCuts(forward.diagram, forwardPrimitiveBody),
    'forward standing hypotheses',
  )
  const forwardConclusion = exactOne(
    directCuts(forward.diagram, forwardHypotheses).filter((region) =>
      scopedWires(forward.diagram, region).length === 0),
    'forward support conclusion',
  )
  const forwardBase = exactOne(
    directCuts(forward.diagram, forwardConclusion).filter((region) =>
      scopedWires(forward.diagram, region).length === 1),
    'forward carrier base',
  )
  const forwardClosure = exactOne(
    directCuts(forward.diagram, forwardConclusion).filter((region) =>
      scopedWires(forward.diagram, region).length === 2),
    'forward carrier closure',
  )
  const forwardZero = relationWire(
    forward.diagram,
    forwardPrimitiveScope,
    UNARY,
  )
  const forwardPlus = relationWire(
    forward.diagram,
    forwardPrimitiveScope,
    TERNARY,
  )

  let before = forward.diagram
  forward.record('introduce plusSingleValued hypothesis handle', {
    rule: 'vacuity',
    direction: 'insert',
    assembly: bareWireAssembly('plusSingleValued', forwardHypotheses, relSig([])),
  })
  const plusSingleValued = onlyNewWire(
    before,
    forward.diagram,
    forwardHypotheses,
  )
  forward.record('assert plusSingleValued hypothesis handle', {
    rule: 'atomSpawn',
    region: forwardHypotheses,
    wire: plusSingleValued,
  })
  forward.recordRelationJoin('ground exact plusSingleValued hypothesis', {
    wire: plusSingleValued,
      content: plusSingleValuedContent(),
      parameters: [forwardPlus],
  })

  forward.record('open right-unit claim scope and body', {
    rule: 'doubleCutIntro',
    sel: {
      region: forwardConclusion,
      regions: [],
      nodes: [],
      wires: [],
    },
  })
  const forwardClaimScope = onlyNewCut(
    before,
    forward.diagram,
    forwardConclusion,
  )
  const forwardClaimBody = exactOne(
    directCuts(forward.diagram, forwardClaimScope),
    'forward claim body',
  )
  for (const label of ['zero value', 'addend', 'output']) {
    forward.record(`introduce forward claim ${label}`, {
      rule: 'vacuity',
      direction: 'insert',
      assembly: bareWireAssembly('claimVariable', forwardClaimScope, IOTA),
    })
  }
  const [forwardClaimZero, forwardAddend, forwardOutput] =
    scopedWires(forward.diagram, forwardClaimScope)
  if (
    forwardClaimZero === undefined
    || forwardAddend === undefined
    || forwardOutput === undefined
  ) throw new Error('missing forward right-unit claim variables')

  before = forward.diagram
  forward.record('open right-unit claim implication', {
    rule: 'doubleCutIntro',
    sel: {
      region: forwardClaimBody,
      regions: [],
      nodes: [],
      wires: [],
    },
  })
  const forwardClaimAntecedent = onlyNewCut(
    before,
    forward.diagram,
    forwardClaimBody,
  )
  const forwardClaimConsequent = exactOne(
    directCuts(forward.diagram, forwardClaimAntecedent),
    'forward claim consequent',
  )

  for (const [label, region] of [
    ['base', forwardBase],
    ['closure', forwardClosure],
  ] as const) {
    forward.record(`copy carrier-support ${label} into claim`, {
      rule: 'iteration',
      sel: {
        region: forwardConclusion,
        regions: [region],
        nodes: [],
        wires: [],
      },
      target: forwardClaimAntecedent,
      })
  }
  forward.record('erase positive carrier-support sources', {
    rule: 'erasure',
    sel: {
      region: forwardConclusion,
      regions: [forwardBase, forwardClosure],
      nodes: [],
      wires: [],
    },
  })

  before = forward.diagram
  forward.record('spawn midpoint claim Zero', {
    rule: 'atomSpawn',
    region: forwardClaimAntecedent,
    wire: forwardZero,
  })
  const forwardClaimZeroNode = onlyNewNode(
    before,
    forward.diagram,
    forwardClaimAntecedent,
  )
  forward.record('attach midpoint claim Zero', {
    rule: 'wireJoin',
    input: {
      a: forwardClaimZero,
      b: endpointWire(
        forward.diagram,
        forwardClaimZeroNode,
        'arg',
        0,
      ),
    },
  })

  const spawnForwardPlus = (
    label: string,
    output: WireId,
  ): NodeId => {
    const prior = forward.diagram
    forward.record(`spawn ${label}`, {
      rule: 'atomSpawn',
      region: forwardClaimAntecedent,
      wire: forwardPlus,
    })
    const node = onlyNewNode(
      prior,
      forward.diagram,
      forwardClaimAntecedent,
    )
    for (const [index, wire] of [
      [0, forwardAddend],
      [1, forwardClaimZero],
      [2, output],
    ] as const) {
      forward.record(`attach ${label} argument ${index}`, {
        rule: 'wireJoin',
        input: {
          a: wire,
          b: endpointWire(forward.diagram, node, 'arg', index),
        },
      })
    }
    return node
  }
  spawnForwardPlus('midpoint claimed Plus', forwardOutput)
  spawnForwardPlus('midpoint canonical Plus', forwardAddend)

  before = forward.diagram
  forward.record('insert midpoint output/addend identity', {
    rule: 'identityInsert',
    region: forwardClaimAntecedent,
    wires: [forwardOutput, forwardAddend],
  })
  const forwardIdentity = onlyNewNode(
    before,
    forward.diagram,
    forwardClaimAntecedent,
  )
  forward.record('copy midpoint identity to consequent', {
    rule: 'iteration',
    sel: {
      region: forwardClaimAntecedent,
      regions: [],
      nodes: [forwardIdentity],
      wires: [],
    },
    target: forwardClaimConsequent,
  })

  const rhs = statements.plusRightUnit
  const backward = new PrimitiveStepRecorder(
    rhs,
    context,
    'backward',
  )
  const primitiveScope = exactOne(
    directCuts(backward.diagram, backward.diagram.root),
    'reviewed primitive scope',
  )
  const primitiveBody = exactOne(
    directCuts(backward.diagram, primitiveScope),
    'reviewed primitive body',
  )
  const hypotheses = exactOne(
    directCuts(backward.diagram, primitiveBody),
    'reviewed standing hypotheses',
  )
  const hypothesisChildren = directCuts(backward.diagram, hypotheses)
  const conclusion = exactOne(
    hypothesisChildren.filter((region) =>
      scopedWires(backward.diagram, region).length === 0),
    'reviewed right-unit conclusion',
  )
  const additionFunctional = exactOne(
    hypothesisChildren.filter((region) =>
      scopedWires(backward.diagram, region).length === 4),
    'reviewed plusSingleValued hypothesis',
  )
  const claimScope = exactOne(
    directCuts(backward.diagram, conclusion),
    'reviewed claim scope',
  )
  const claimBody = exactOne(
    directCuts(backward.diagram, claimScope),
    'reviewed claim body',
  )
  const claimAntecedent = exactOne(
    directCuts(backward.diagram, claimBody),
    'reviewed claim antecedent',
  )
  const reviewedZero = relationWire(
    backward.diagram,
    primitiveScope,
    UNARY,
  )
  const reviewedSuccessor = relationWire(
    backward.diagram,
    primitiveScope,
    BINARY,
  )
  const reviewedPlus = relationWire(
    backward.diagram,
    primitiveScope,
    TERNARY,
  )
  const [claimZero, claimAddend, claimOutput] =
    scopedWires(backward.diagram, claimScope)
  if (
    claimZero === undefined
    || claimAddend === undefined
    || claimOutput === undefined
  ) throw new Error('missing reviewed right-unit claim variables')

  before = backward.diagram
  backward.record('cite direct carrier inductivity in claim', {
    rule: 'theorem',
    name: 'rightIdentityCarrierInductive',
    direction: 'forward',
    at: {
      sel: {
        region: claimAntecedent,
        regions: [],
        nodes: [],
        wires: [],
      },
      args: [],
    },
  })
  const citedScope = onlyNewCut(
    before,
    backward.diagram,
    claimAntecedent,
  )
  const citedBody = exactOne(
    directCuts(backward.diagram, citedScope),
    'cited primitive body',
  )
  const citedHypotheses = exactOne(
    directCuts(backward.diagram, citedBody),
    'cited standing hypotheses',
  )
  const citedConclusion = exactOne(
    directCuts(backward.diagram, citedHypotheses).filter((region) =>
      scopedWires(backward.diagram, region).length === 0),
    'cited support conclusion',
  )

  for (const [outer, inner, signature] of [
    [
      reviewedZero,
      relationWire(backward.diagram, citedScope, UNARY),
      UNARY,
    ],
    [
      reviewedSuccessor,
      relationWire(backward.diagram, citedScope, BINARY),
      BINARY,
    ],
    [
      reviewedPlus,
      relationWire(backward.diagram, citedScope, TERNARY),
      TERNARY,
    ],
  ] as const) {
    backward.recordRelationJoin('specialize cited primitive relation', {
    wire: inner,
        content: relationApplicationContent(signature),
        parameters: [outer],
  })
  }

  for (const citedHypothesis of directCuts(
    backward.diagram,
    citedHypotheses,
  ).filter((region) => region !== citedConclusion)) {
    const sel = {
      region: citedHypotheses,
      regions: [citedHypothesis],
      nodes: [],
      wires: [],
    } as const
    const evidence = findDeiterationEvidence(
      backward.diagram,
      sel,
    )
    backward.record('discharge cited primitive hypothesis', {
      rule: 'deiteration',
      sel,
      justifier: evidence.justifier,
      certificate: evidence.certificate,
      })
  }
  backward.record('expose cited carrier-support conclusion', {
    rule: 'doubleCutElim',
    region: citedHypotheses,
  })
  backward.record('remove cited primitive scope', {
    rule: 'doubleCutElim',
    region: citedScope,
  })

  const externalBase = exactOne(
    directCuts(backward.diagram, claimAntecedent).filter((region) =>
      scopedWires(backward.diagram, region).length === 1),
    'external carrier base',
  )
  const externalClosure = exactOne(
    directCuts(backward.diagram, claimAntecedent).filter((region) =>
      scopedWires(backward.diagram, region).length === 2),
    'external carrier closure',
  )
  const claimNat = exactOne(
    directNodes(backward.diagram, claimAntecedent).filter((node) =>
      backward.diagram.nodes[node]!.kind === 'ref'
      && backward.diagram.nodes[node]!.defId === 'nat'),
    'reviewed Nat premise',
  )
  backward.record('unfold Nat for direct carrier grounding', {
    rule: 'unfold',
    nodeId: claimNat,
  })
  const propertyScope = exactOne(
    directCuts(backward.diagram, claimAntecedent).filter((region) =>
      scopedWires(backward.diagram, region).some((wire) =>
        backward.diagram.wires[wire]!.sig.kind === 'rel')),
    'unfolded Nat property scope',
  )
  const propertyBody = exactOne(
    directCuts(backward.diagram, propertyScope),
    'unfolded Nat property body',
  )
  const property = relationWire(
    backward.diagram,
    propertyScope,
    UNARY,
  )
  backward.recordRelationJoin('ground Nat property directly to right identity', {
    wire: property,
      content: rightIdentityCarrierContent(),
      parameters: [reviewedZero, reviewedPlus],
  })

  const hereditary = exactOne(
    directCuts(backward.diagram, propertyBody),
    'Nat hereditary implication',
  )
  const hereditaryChildren = directCuts(backward.diagram, hereditary)
  const nestedBase = exactOne(
    hereditaryChildren.filter((region) =>
      scopedWires(backward.diagram, region).length === 1),
    'nested carrier base',
  )
  const nestedClosure = exactOne(
    hereditaryChildren.filter((region) =>
      scopedWires(backward.diagram, region).length === 2),
    'nested carrier closure',
  )
  for (const [label, region] of [
    ['base', nestedBase],
    ['closure', nestedClosure],
  ] as const) {
    const sel = {
      region: hereditary,
      regions: [region],
      nodes: [],
      wires: [],
    } as const
    const evidence = findDeiterationEvidence(
      backward.diagram,
      sel,
    )
    backward.record(`discharge Nat carrier ${label} from support`, {
      rule: 'deiteration',
      sel,
      justifier: evidence.justifier,
      certificate: evidence.certificate,
      })
  }
  backward.record('expose inherited direct carrier', {
    rule: 'doubleCutElim',
    region: hereditary,
  })
  backward.record('remove grounded Nat property scope', {
    rule: 'doubleCutElim',
    region: propertyScope,
  })

  const inheritedE = exactOne(
    directCuts(backward.diagram, claimAntecedent).filter((region) => {
      if (scopedWires(backward.diagram, region).length !== 1) {
        return false
      }
      const bodies = directCuts(backward.diagram, region)
      if (bodies.length !== 1) return false
      const antecedents = directCuts(backward.diagram, bodies[0]!)
      if (antecedents.length !== 1) return false
      const consequents = directCuts(backward.diagram, antecedents[0]!)
      return consequents.length === 1
        && directNodes(backward.diagram, consequents[0]!).some((node) =>
          backward.diagram.nodes[node]!.kind === 'atom'
          && endpointWire(backward.diagram, node, 'head') === reviewedPlus)
    }),
    'inherited direct right-identity carrier',
  )
  const inheritedEBody = exactOne(
    directCuts(backward.diagram, inheritedE),
    'inherited E body',
  )
  const inheritedEAntecedent = exactOne(
    directCuts(backward.diagram, inheritedEBody),
    'inherited E antecedent',
  )
  const inheritedLocalZero = exactOne(
    scopedWires(backward.diagram, inheritedE),
    'inherited E local zero',
  )
  backward.record('specialize inherited E at claim zero', {
    rule: 'wireJoin',
    input: {
      a: claimZero,
      b: inheritedLocalZero,
    },
  })
  deiterateNode(
    backward,
    'discharge inherited E Zero',
    inheritedEAntecedent,
    exactOne(
      directNodes(backward.diagram, inheritedEAntecedent),
      'inherited E Zero premise',
    ),
  )
  backward.record('expose inherited canonical Plus', {
    rule: 'doubleCutElim',
    region: inheritedEAntecedent,
  })
  backward.record('remove inherited E scope', {
    rule: 'doubleCutElim',
    region: inheritedE,
  })

  before = backward.diagram
  backward.record('copy addition functionality into claim', {
    rule: 'iteration',
    sel: {
      region: hypotheses,
      regions: [additionFunctional],
      nodes: [],
      wires: [],
    },
    target: claimAntecedent,
  })
  const copiedFunctional = onlyNewCut(
    before,
    backward.diagram,
    claimAntecedent,
  )
  const copiedFunctionalBody = exactOne(
    directCuts(backward.diagram, copiedFunctional),
    'copied addition-functional body',
  )
  const copiedFunctionalAntecedent = exactOne(
    directCuts(backward.diagram, copiedFunctionalBody),
    'copied addition-functional antecedent',
  )
  const copiedVariables = scopedWires(
    backward.diagram,
    copiedFunctional,
  )
  if (copiedVariables.length !== 4) {
    throw new Error('expected four addition-functional variables')
  }
  for (const [label, outer, inner] of [
    ['left', claimAddend, copiedVariables[0]!],
    ['right', claimZero, copiedVariables[1]!],
    ['first output', claimOutput, copiedVariables[2]!],
    ['second output', claimAddend, copiedVariables[3]!],
  ] as const) {
    backward.record(`specialize addition-functional ${label}`, {
      rule: 'wireJoin',
      input: {
        a: outer,
        b: inner,
      },
    })
  }
  for (const node of directNodes(
    backward.diagram,
    copiedFunctionalAntecedent,
  )) {
    deiterateNode(
      backward,
      'discharge addition-functional premise',
      copiedFunctionalAntecedent,
      node,
    )
  }
  backward.record('expose output/addend identity', {
    rule: 'doubleCutElim',
    region: copiedFunctionalAntecedent,
  })
  backward.record('remove copied addition functionality', {
    rule: 'doubleCutElim',
    region: copiedFunctional,
  })

  void externalBase
  void externalClosure
  return {
    name: 'plusRightUnit',
    lhs,
    rhs,
    actions: forward.actions,
    backActions: backward.actions,
  }
}

export function buildRightUnitTheorem(
  relations: Theory['relations'],
  prefix: readonly Theorem[],
  statements: ArithmeticStatements,
): readonly Theorem[] {
  let context = verifyTheory({ relations, theorems: prefix })
  const carrierInductive = rightIdentityCarrierInductive(
    statements,
    context,
  )
  context = registerTheorem(context, carrierInductive)
  const rightUnit = plusRightUnit(statements, context)
  context = registerTheorem(context, rightUnit)
  void context
  return Object.freeze([carrierInductive, rightUnit])
}
