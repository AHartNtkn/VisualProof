import { IOTA } from '../kernel/diagram/sig'
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
  successorShiftCarrierContent,
  scopedWires,
} from './arithmetic-support'
import {
  emptyGraph,
  finishDiagramWithBoundary,
} from './graph'
import {
  PrimitiveStepRecorder,
  onlyNewCut,
  onlyNewNode,
  onlyNewWire,
} from './record'
import {
  successorShiftCarrierInductive,
} from './arithmetic-shift-carrier'
import type { ArithmeticStatements } from './statements'

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
    4096,
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
function succShiftS(
  statements: ArithmeticStatements,
  context: ProofContext,
): Theorem {
  const lhs = finishDiagramWithBoundary(emptyGraph(), [])
  const forward = new PrimitiveStepRecorder(lhs.diagram, context)

  forward.record('seed successor-shift shell from direct carrier support', {
    rule: 'theorem',
    name: 'successorShiftCarrierInductive',
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
  const forwardSuccessor = relationWire(
    forward.diagram,
    forwardPrimitiveScope,
    BINARY,
  )
  const forwardPlus = relationWire(
    forward.diagram,
    forwardPrimitiveScope,
    TERNARY,
  )

  let before = forward.diagram
  forward.record('open successor-shift claim scope and body', {
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
  for (const label of ['left', 'right', 'right successor', 'output']) {
    forward.record(`introduce forward claim ${label}`, {
      rule: 'vacuity',
      direction: 'insert',
      assembly: bareWireAssembly('claimVariable', forwardClaimScope, IOTA),
    })
  }
  const [
    forwardLeft,
    forwardRight,
    forwardRightSuccessor,
    forwardOutput,
  ] =
    scopedWires(forward.diagram, forwardClaimScope)
  if (
    forwardLeft === undefined
    || forwardRight === undefined
    || forwardRightSuccessor === undefined
    || forwardOutput === undefined
  ) throw new Error('missing forward successor-shift claim variables')

  before = forward.diagram
  forward.record('open successor-shift claim implication', {
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

  const spawnForwardAtom = (
    label: string,
    relation: WireId,
    args: readonly WireId[],
  ): NodeId => {
    const prior = forward.diagram
    forward.record(`spawn ${label}`, {
      rule: 'atomSpawn',
      region: forwardClaimAntecedent,
      wire: relation,
    })
    const node = onlyNewNode(
      prior,
      forward.diagram,
      forwardClaimAntecedent,
    )
    args.forEach((wire, index) => {
      forward.record(`attach ${label} argument ${index}`, {
        rule: 'wireJoin',
        input: {
          a: wire,
          b: endpointWire(forward.diagram, node, 'arg', index),
        },
      })
    })
    return node
  }

  before = forward.diagram
  forward.record('introduce midpoint predecessor sum', {
    rule: 'vacuity',
    direction: 'insert',
    assembly: bareWireAssembly('predecessorSum', forwardClaimAntecedent, IOTA),
  })
  const forwardPredecessorSum = onlyNewWire(
    before,
    forward.diagram,
    forwardClaimAntecedent,
  )
  before = forward.diagram
  forward.record('introduce midpoint predecessor sum successor', {
    rule: 'vacuity',
    direction: 'insert',
    assembly: bareWireAssembly(
      'predecessorSumSuccessor',
      forwardClaimAntecedent,
      IOTA,
    ),
  })
  const forwardPredecessorSumSuccessor = onlyNewWire(
    before,
    forward.diagram,
    forwardClaimAntecedent,
  )
  spawnForwardAtom(
    'midpoint right successor premise',
    forwardSuccessor,
    [forwardRight, forwardRightSuccessor],
  )
  spawnForwardAtom(
    'midpoint claimed shifted addition',
    forwardPlus,
    [forwardLeft, forwardRightSuccessor, forwardOutput],
  )
  spawnForwardAtom(
    'midpoint inherited totality result',
    forwardPlus,
    [forwardLeft, forwardRight, forwardPredecessorSum],
  )
  spawnForwardAtom(
    'midpoint predecessor output successor',
    forwardSuccessor,
    [forwardPredecessorSum, forwardPredecessorSumSuccessor],
  )
  spawnForwardAtom(
    'midpoint inherited shift result',
    forwardPlus,
    [
      forwardLeft,
      forwardRightSuccessor,
      forwardPredecessorSumSuccessor,
    ],
  )

  // id(claimed output, predecessor-sum successor) has one outer wire; the
  // one-point collapse merges them on the spot, leaving no identity node.
  forward.record('insert midpoint output identity', {
    rule: 'identityInsert',
    region: forwardClaimAntecedent,
    wires: [forwardOutput, forwardPredecessorSumSuccessor],
  })
  void forwardZero
  void forwardClaimConsequent

  const rhs = statements.succShiftS
  const backward = new PrimitiveStepRecorder(
    rhs.diagram,
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
    'reviewed successor-shift conclusion',
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
  const claimConsequent = exactOne(
    directCuts(backward.diagram, claimAntecedent),
    'reviewed claim consequent',
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
  const [claimLeft, claimRight, claimRightSuccessor, claimOutput] =
    scopedWires(backward.diagram, claimScope)
  if (
    claimLeft === undefined
    || claimRight === undefined
    || claimRightSuccessor === undefined
    || claimOutput === undefined
  ) throw new Error('missing reviewed successor-shift claim variables')

  before = backward.diagram
  backward.record('cite direct carrier inductivity in claim', {
    rule: 'theorem',
    name: 'successorShiftCarrierInductive',
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
      4096,
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
      region !== claimConsequent
      &&
      scopedWires(backward.diagram, region).length === 1),
    'external carrier base',
  )
  const externalClosure = exactOne(
    directCuts(backward.diagram, claimAntecedent).filter((region) =>
      region !== claimConsequent
      &&
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
  backward.recordRelationJoin('ground Nat property directly to successor shift', {
    wire: property,
      content: successorShiftCarrierContent(),
      parameters: [reviewedSuccessor, reviewedPlus],
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
      4096,
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

  const inheritedCarrierScopes = directCuts(
    backward.diagram,
    claimAntecedent,
  ).filter((region) =>
    region !== claimConsequent
    && region !== externalBase
    && region !== externalClosure)
  const inheritedTotality = exactOne(
    inheritedCarrierScopes.filter((region) =>
      scopedWires(backward.diagram, region).length === 1),
    'inherited successor-shift totality',
  )
  const inheritedTransport = exactOne(
    inheritedCarrierScopes.filter((region) =>
      scopedWires(backward.diagram, region).length === 4),
    'inherited successor-shift transport',
  )
  backward.record('specialize inherited totality at claim right', {
    rule: 'wireJoin',
    input: {
      a: claimRight,
      b: exactOne(
        scopedWires(backward.diagram, inheritedTotality),
        'inherited totality right input',
      ),
    },
  })
  const inheritedTotalityBody = exactOne(
    directCuts(backward.diagram, inheritedTotality),
    'inherited totality body',
  )
  const inheritedAddition = exactOne(
    directNodes(backward.diagram, inheritedTotalityBody),
    'inherited totality addition',
  )
  const predecessorSum = endpointWire(
    backward.diagram,
    inheritedAddition,
    'arg',
    2,
  )
  backward.record('expose inherited predecessor sum', {
    rule: 'doubleCutElim',
    region: inheritedTotality,
  })

  const successorTotal = exactOne(
    hypothesisChildren.filter((region) =>
      scopedWires(backward.diagram, region).length === 1),
    'reviewed successorTotal hypothesis',
  )
  before = backward.diagram
  backward.record('copy successor totality into claim', {
    rule: 'iteration',
    sel: {
      region: hypotheses,
      regions: [successorTotal],
      nodes: [],
      wires: [],
    },
    target: claimAntecedent,
  })
  const copiedSuccessorTotal = onlyNewCut(
    before,
    backward.diagram,
    claimAntecedent,
  )
  const copiedSuccessorTotalBody = exactOne(
    directCuts(backward.diagram, copiedSuccessorTotal),
    'copied successor-totality body',
  )
  const predecessorSumSuccessorNode = exactOne(
    directNodes(backward.diagram, copiedSuccessorTotalBody),
    'copied predecessor-sum successor',
  )
  backward.record('specialize predecessor-sum successor input', {
    rule: 'wireJoin',
    input: {
      a: predecessorSum,
      b: endpointWire(
        backward.diagram,
        predecessorSumSuccessorNode,
        'arg',
        0,
      ),
    },
  })
  const predecessorSumSuccessor = endpointWire(
    backward.diagram,
    predecessorSumSuccessorNode,
    'arg',
    1,
  )
  backward.record('expose predecessor-sum successor', {
    rule: 'doubleCutElim',
    region: copiedSuccessorTotal,
  })

  const inheritedTransportBody = exactOne(
    directCuts(backward.diagram, inheritedTransport),
    'inherited transport body',
  )
  const inheritedTransportAntecedent = exactOne(
    directCuts(backward.diagram, inheritedTransportBody),
    'inherited transport antecedent',
  )
  const inheritedTransportConsequent = exactOne(
    directCuts(backward.diagram, inheritedTransportAntecedent),
    'inherited transport consequent',
  )
  const inheritedTransportPremises = directNodes(
    backward.diagram,
    inheritedTransportAntecedent,
  )
  const inheritedTransportPlus = exactOne(
    inheritedTransportPremises.filter((node) =>
      endpointWire(backward.diagram, node, 'head') === reviewedPlus),
    'inherited transport Plus premise',
  )
  const inheritedTransportSuccessors =
    inheritedTransportPremises.filter((node) =>
      endpointWire(backward.diagram, node, 'head') === reviewedSuccessor)
  const inheritedRight = endpointWire(
    backward.diagram,
    inheritedTransportPlus,
    'arg',
    1,
  )
  const inheritedOutput = endpointWire(
    backward.diagram,
    inheritedTransportPlus,
    'arg',
    2,
  )
  const inheritedRightSuccessorNode = exactOne(
    inheritedTransportSuccessors.filter((node) =>
      endpointWire(backward.diagram, node, 'arg', 0) === inheritedRight),
    'inherited right successor',
  )
  const inheritedOutputSuccessorNode = exactOne(
    inheritedTransportSuccessors.filter((node) =>
      endpointWire(backward.diagram, node, 'arg', 0) === inheritedOutput),
    'inherited output successor',
  )
  for (const [label, outer, inner] of [
    ['right', claimRight, inheritedRight],
    [
      'right successor',
      claimRightSuccessor,
      endpointWire(
        backward.diagram,
        inheritedRightSuccessorNode,
        'arg',
        1,
      ),
    ],
    ['output', predecessorSum, inheritedOutput],
    [
      'output successor',
      predecessorSumSuccessor,
      endpointWire(
        backward.diagram,
        inheritedOutputSuccessorNode,
        'arg',
        1,
      ),
    ],
  ] as const) {
    backward.record(`specialize inherited transport ${label}`, {
      rule: 'wireJoin',
      input: { a: outer, b: inner },
    })
  }
  for (const node of [
    inheritedTransportPlus,
    inheritedRightSuccessorNode,
    inheritedOutputSuccessorNode,
  ]) {
    deiterateNode(
      backward,
      'discharge inherited transport premise',
      inheritedTransportAntecedent,
      node,
    )
  }
  const inheritedShiftResult = exactOne(
    directNodes(backward.diagram, inheritedTransportConsequent),
    'inherited shift result',
  )
  backward.record('expose inherited shift result', {
    rule: 'doubleCutElim',
    region: inheritedTransportAntecedent,
  })
  backward.record('finish inherited transport specialization', {
    rule: 'doubleCutElim',
    region: inheritedTransport,
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
  const copiedFunctionalConsequent = exactOne(
    directCuts(backward.diagram, copiedFunctionalAntecedent),
    'copied addition-functional consequent',
  )
  const copiedVariables = scopedWires(
    backward.diagram,
    copiedFunctional,
  )
  if (copiedVariables.length !== 4) {
    throw new Error('expected four addition-functional variables')
  }
  for (const [label, outer, inner] of [
    ['left', claimLeft, copiedVariables[0]!],
    ['right', claimRightSuccessor, copiedVariables[1]!],
    ['first output', claimOutput, copiedVariables[2]!],
    ['second output', predecessorSumSuccessor, copiedVariables[3]!],
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
  exactOne(
    directNodes(backward.diagram, copiedFunctionalConsequent),
    'output identity',
  )
  backward.record('expose output identity', {
    rule: 'doubleCutElim',
    region: copiedFunctionalAntecedent,
  })
  // Removing the functionality shell exposes id(predecessor-sum successor,
  // claim output) with one outer wire; the one-point collapse merges them
  // on the spot, so the successor goal discharges directly below.
  backward.record('remove copied addition functionality', {
    rule: 'doubleCutElim',
    region: copiedFunctional,
  })

  const claimGoals = directNodes(backward.diagram, claimConsequent)
  const claimPredecessorAddition = exactOne(
    claimGoals.filter((node) =>
      endpointWire(backward.diagram, node, 'head') === reviewedPlus),
    'claim predecessor addition',
  )
  const claimPredecessorSuccessor = exactOne(
    claimGoals.filter((node) =>
      endpointWire(backward.diagram, node, 'head') === reviewedSuccessor),
    'claim predecessor successor',
  )
  backward.record('choose inherited predecessor sum as claim witness', {
    rule: 'wireJoin',
    input: {
      a: predecessorSum,
      b: endpointWire(
        backward.diagram,
        claimPredecessorAddition,
        'arg',
        2,
      ),
    },
  })
  deiterateNode(
    backward,
    'discharge claim predecessor addition',
    claimConsequent,
    claimPredecessorAddition,
  )
  deiterateNode(
    backward,
    'discharge claim predecessor successor',
    claimConsequent,
    claimPredecessorSuccessor,
  )

  void externalBase
  void externalClosure
  void inheritedShiftResult
  return {
    name: 'succShiftS',
    lhs,
    rhs,
    actions: forward.actions,
    backActions: backward.actions,
  }
}

export function buildSuccessorShiftTheorem(
  relations: Theory['relations'],
  prefix: readonly Theorem[],
  statements: ArithmeticStatements,
): readonly Theorem[] {
  let context = verifyTheory({ relations, theorems: prefix })
  const carrierInductive = successorShiftCarrierInductive(
    statements,
    context,
  )
  context = registerTheorem(context, carrierInductive)
  const rightUnit = succShiftS(statements, context)
  context = registerTheorem(context, rightUnit)
  void context
  return Object.freeze([carrierInductive, rightUnit])
}
