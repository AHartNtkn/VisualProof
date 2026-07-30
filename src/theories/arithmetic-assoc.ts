import { extractSubgraph } from '../kernel/diagram/subgraph/extract'
import { IOTA, relSig } from '../kernel/diagram/sig'
import { findDeiterationEvidence } from '../kernel/rules/iteration'
import {
  registerTheorem,
  verifyTheory,
  type ProofContext,
  type Theory,
} from '../kernel/proof/context'
import type { Theorem } from '../kernel/proof/theorem'
import {
  BINARY,
  TERNARY,
  UNARY,
  associativityCarrierContent,
  deiterationStep,
  directCuts,
  directNodes,
  endpointWire,
  exactOne,
  relationApplicationContent,
  relationWire,
  scopedWires,
} from './arithmetic-support'
import {
  atom,
  declareWire,
  emptyGraph,
  finishDiagramWithBoundary,
  implication,
  quantifierScope,
} from './graph'
import {
  PrimitiveStepRecorder,
  onlyNewCut,
  onlyNewNode,
  onlyNewWire,
} from './record'
import { associativityCarrierBase } from './arithmetic-assoc-base'
import {
  associativityCarrierHereditary,
} from './arithmetic-assoc-carrier'
import type { ArithmeticStatements } from './statements'

function plusBaseContent() {
  let graph = emptyGraph()
  const zero = declareWire(graph, graph.root, UNARY)
  graph = zero.graph
  const plus = declareWire(graph, graph.root, TERNARY)
  graph = plus.graph
  const variables = quantifierScope(
    graph,
    graph.root,
    'forall',
    [IOTA, IOTA],
  )
  graph = variables.graph
  const [zeroValue, right] = variables.value.variables
  const claim = implication(graph, variables.value.body)
  graph = claim.graph
  graph = atom(
    graph,
    claim.value.antecedent,
    zero.value,
    [zeroValue!],
  ).graph
  graph = atom(
    graph,
    claim.value.consequent,
    plus.value,
    [zeroValue!, right!, right!],
  ).graph
  return finishDiagramWithBoundary(graph, [zero.value, plus.value])
}

function associativityTransportContent() {
  let graph = emptyGraph()
  const formal = declareWire(graph, graph.root, IOTA)
  graph = formal.graph
  const plus = declareWire(graph, graph.root, TERNARY)
  graph = plus.graph
  const transport = quantifierScope(
    graph,
    graph.root,
    'forall',
    [IOTA, IOTA, IOTA, IOTA],
  )
  const [right, third, firstSum, innerSum] =
    transport.value.variables
  const claim = implication(transport.graph, transport.value.body)
  graph = atom(
    claim.graph,
    claim.value.antecedent,
    plus.value,
    [formal.value, right!, firstSum!],
  ).graph
  graph = atom(
    graph,
    claim.value.antecedent,
    plus.value,
    [right!, third!, innerSum!],
  ).graph
  const output = declareWire(graph, claim.value.consequent, IOTA)
  graph = atom(
    output.graph,
    claim.value.consequent,
    plus.value,
    [firstSum!, third!, output.value],
  ).graph
  graph = atom(
    graph,
    claim.value.consequent,
    plus.value,
    [formal.value, innerSum!, output.value],
  ).graph
  return finishDiagramWithBoundary(
    graph,
    [formal.value, plus.value],
  )
}


function plusAssoc(
  statements: ArithmeticStatements,
  context: ProofContext,
): Theorem {
  const publicLhs = finishDiagramWithBoundary(emptyGraph(), [])
  const publicForward = new PrimitiveStepRecorder(
    publicLhs.diagram,
    context,
  )
  publicForward.record('seed public shell from hereditary support', {
    rule: 'theorem',
    name: 'associativityCarrierHereditary',
    direction: 'forward',
    at: {
      sel: {
        region: publicForward.diagram.root,
        regions: [],
        nodes: [],
        wires: [],
      },
      args: [],
    },
  })
  const publicPrimitiveScope = exactOne(
    directCuts(publicForward.diagram, publicForward.diagram.root),
    'public primitive scope',
  )
  const publicPrimitiveBody = exactOne(
    directCuts(publicForward.diagram, publicPrimitiveScope),
    'public primitive body',
  )
  const publicHypotheses = exactOne(
    directCuts(publicForward.diagram, publicPrimitiveBody),
    'public hypotheses',
  )
  const publicConclusion = exactOne(
    directCuts(publicForward.diagram, publicHypotheses).filter((region) =>
      scopedWires(publicForward.diagram, region).length === 0),
    'public support conclusion',
  )
  let publicBefore = publicForward.diagram
  publicForward.record('introduce public zero relation', {
    rule: 'vacuousIntro',
    scope: publicPrimitiveScope,
    sig: UNARY,
  })
  const publicZero = onlyNewWire(
    publicBefore,
    publicForward.diagram,
    publicPrimitiveScope,
  )
  const publicPlus = relationWire(
    publicForward.diagram,
    publicPrimitiveScope,
    TERNARY,
  )
  publicBefore = publicForward.diagram
  publicForward.record('introduce plusBase hypothesis handle', {
    rule: 'vacuousIntro',
    scope: publicHypotheses,
    sig: relSig([]),
  })
  const plusBase = onlyNewWire(
    publicBefore,
    publicForward.diagram,
    publicHypotheses,
  )
  publicForward.record('assert plusBase hypothesis handle', {
    rule: 'atomSpawn',
    region: publicHypotheses,
    wire: plusBase,
  })
  publicForward.recordRelationJoin('ground exact plusBase hypothesis', {
    wire: plusBase,
      content: plusBaseContent(),
      parameters: [publicZero, publicPlus],
  })

  publicBefore = publicForward.diagram
  publicForward.record('cite exact carrier base in positive conclusion', {
    rule: 'theorem',
    name: 'associativityCarrierBase',
    direction: 'forward',
    at: {
      sel: {
        region: publicConclusion,
        regions: [],
        nodes: [],
        wires: [],
      },
      args: [],
    },
  })
  const citedBaseScope = onlyNewCut(
    publicBefore,
    publicForward.diagram,
    publicConclusion,
  )
  const citedBaseBody = exactOne(
    directCuts(publicForward.diagram, citedBaseScope),
    'cited base primitive body',
  )
  const citedBaseHypotheses = exactOne(
    directCuts(publicForward.diagram, citedBaseBody),
    'cited base hypotheses',
  )
  const citedBaseConclusion = exactOne(
    directCuts(publicForward.diagram, citedBaseHypotheses).filter((region) =>
      scopedWires(publicForward.diagram, region).length === 0),
    'cited base conclusion',
  )
  for (const [outer, inner, signature] of [
    [
      publicZero,
      relationWire(publicForward.diagram, citedBaseScope, UNARY),
      UNARY,
    ],
    [
      publicPlus,
      relationWire(publicForward.diagram, citedBaseScope, TERNARY),
      TERNARY,
    ],
  ] as const) {
    publicForward.recordRelationJoin('specialize cited base primitive', {
    wire: inner,
        content: relationApplicationContent(signature),
        parameters: [outer],
  })
  }
  for (const citedHypothesis of directCuts(
    publicForward.diagram,
    citedBaseHypotheses,
  ).filter((region) => region !== citedBaseConclusion)) {
    const sel = {
      region: citedBaseHypotheses,
      regions: [citedHypothesis],
      nodes: [],
      wires: [],
    } as const
    const evidence = findDeiterationEvidence(
      publicForward.diagram,
      sel,
      4096,
    )
    publicForward.record('discharge cited base standing hypothesis', {
      rule: 'deiteration',
      sel,
      justifier: evidence.justifier,
      certificate: evidence.certificate,
      retargets: [],
    })
  }
  publicForward.record('expose exact cited carrier base', {
    rule: 'doubleCutElim',
    region: citedBaseHypotheses,
  })
  publicForward.record('remove cited base primitive scope', {
    rule: 'doubleCutElim',
    region: citedBaseScope,
  })
  const exposedBase = exactOne(
    directCuts(publicForward.diagram, publicConclusion).filter((region) =>
      scopedWires(publicForward.diagram, region).length === 1),
    'exposed exact Base(A)',
  )
  const exposedClosure = exactOne(
    directCuts(publicForward.diagram, publicConclusion).filter((region) =>
      scopedWires(publicForward.diagram, region).length === 2),
    'exposed exact Closure(A)',
  )
  publicBefore = publicForward.diagram
  publicForward.record('open public five-binder scope', {
    rule: 'doubleCutIntro',
    sel: {
      region: publicConclusion,
      regions: [],
      nodes: [],
      wires: [],
    },
  })
  const publicClaimScope = onlyNewCut(
    publicBefore,
    publicForward.diagram,
    publicConclusion,
  )
  const publicClaimBody = exactOne(
    directCuts(publicForward.diagram, publicClaimScope),
    'public claim body',
  )
  for (const label of ['left', 'right', 'third', 'first sum', 'output']) {
    publicBefore = publicForward.diagram
    publicForward.record('introduce public ' + label, {
      rule: 'vacuousIntro',
      scope: publicClaimScope,
      sig: IOTA,
    })
    onlyNewWire(publicBefore, publicForward.diagram, publicClaimScope)
  }
  publicBefore = publicForward.diagram
  publicForward.record('open public implication', {
    rule: 'doubleCutIntro',
    sel: {
      region: publicClaimBody,
      regions: [],
      nodes: [],
      wires: [],
    },
  })
  const publicClaimAntecedent = onlyNewCut(
    publicBefore,
    publicForward.diagram,
    publicClaimBody,
  )
  const publicClaimConsequent = exactOne(
    directCuts(publicForward.diagram, publicClaimAntecedent),
    'public claim consequent',
  )
  for (const label of ['left Nat', 'right Nat']) {
    publicForward.record('copy exact carrier base for ' + label, {
      rule: 'iteration',
      sel: {
        region: publicConclusion,
        regions: [exposedBase],
        nodes: [],
        wires: [],
      },
      target: publicClaimAntecedent,
      retargets: [],
    })
  }
  publicForward.record('copy exact carrier closure into claim', {
    rule: 'iteration',
    sel: {
      region: publicConclusion,
      regions: [exposedClosure],
      nodes: [],
      wires: [],
    },
    target: publicClaimAntecedent,
    retargets: [],
  })
  publicForward.record('erase positive support sources', {
    rule: 'erasure',
    sel: {
      region: publicConclusion,
      regions: [exposedBase, exposedClosure],
      nodes: [],
      wires: [],
    },
  })
  const [
    forwardLeft,
    publicForwardRight,
    publicForwardThird,
    forwardFirstSum,
    forwardPublicOutput,
  ] = scopedWires(publicForward.diagram, publicClaimScope)
  const spawnPublic = (
    label: string,
    args: readonly string[],
  ) => {
    const prior = publicForward.diagram
    publicForward.record('spawn ' + label, {
      rule: 'atomSpawn',
      region: publicClaimAntecedent,
      wire: publicPlus,
    })
    const node = onlyNewNode(
      prior,
      publicForward.diagram,
      publicClaimAntecedent,
    )
    args.forEach((wire, index) => {
      publicForward.record('attach ' + label + ' argument ' + index, {
        rule: 'wireJoin',
        input: {
          kind: 'iota',
          a: wire,
          b: endpointWire(publicForward.diagram, node, 'arg', index),
        },
      })
    })
    return node
  }
  spawnPublic(
    'public first premise',
    [forwardLeft!, publicForwardRight!, forwardFirstSum!],
  )
  spawnPublic(
    'public second premise',
    [forwardFirstSum!, publicForwardThird!, forwardPublicOutput!],
  )
  publicBefore = publicForward.diagram
  publicForward.record('introduce public inner sum witness', {
    rule: 'vacuousIntro',
    scope: publicClaimAntecedent,
    sig: IOTA,
  })
  const forwardInnerSum = onlyNewWire(
    publicBefore,
    publicForward.diagram,
    publicClaimAntecedent,
  )
  publicBefore = publicForward.diagram
  publicForward.record('introduce transport output witness', {
    rule: 'vacuousIntro',
    scope: publicClaimAntecedent,
    sig: IOTA,
  })
  const forwardTransportOutput = onlyNewWire(
    publicBefore,
    publicForward.diagram,
    publicClaimAntecedent,
  )
  const forwardDerivedInner = spawnPublic(
    'derived inner sum',
    [publicForwardRight!, publicForwardThird!, forwardInnerSum],
  )
  const forwardRetargetedOuter = spawnPublic(
    'retargeted public outer result',
    [forwardLeft!, forwardInnerSum, forwardPublicOutput!],
  )
  publicForward.record('copy public existential pair to consequent', {
    rule: 'iteration',
    sel: {
      region: publicClaimAntecedent,
      regions: [],
      nodes: [forwardDerivedInner, forwardRetargetedOuter],
      wires: [forwardInnerSum],
    },
    target: publicClaimConsequent,
    retargets: [],
  })
  spawnPublic(
    'transport first result',
    [forwardFirstSum!, publicForwardThird!, forwardTransportOutput],
  )
  spawnPublic(
    'transport outer result',
    [forwardLeft!, forwardInnerSum, forwardTransportOutput],
  )
  publicBefore = publicForward.diagram
  publicForward.record('insert public/transport output identity', {
    rule: 'identityInsert',
    region: publicClaimAntecedent,
    wires: [forwardPublicOutput!, forwardTransportOutput],
  })
  onlyNewNode(
    publicBefore,
    publicForward.diagram,
    publicClaimAntecedent,
  )

  publicBefore = publicForward.diagram
  publicForward.record('open residual A(a) totality', {
    rule: 'doubleCutIntro',
    sel: {
      region: publicClaimAntecedent,
      regions: [],
      nodes: [],
      wires: [],
    },
  })
  const forwardLeftTotality = onlyNewCut(
    publicBefore,
    publicForward.diagram,
    publicClaimAntecedent,
  )
  const forwardLeftTotalityBody = exactOne(
    directCuts(publicForward.diagram, forwardLeftTotality),
    'forward residual A(a) totality body',
  )
  publicBefore = publicForward.diagram
  publicForward.record('introduce residual A(a) totality input', {
    rule: 'vacuousIntro',
    scope: forwardLeftTotality,
    sig: IOTA,
  })
  const forwardLeftTotalityInput = onlyNewWire(
    publicBefore,
    publicForward.diagram,
    forwardLeftTotality,
  )
  publicBefore = publicForward.diagram
  publicForward.record('introduce residual A(a) totality output', {
    rule: 'vacuousIntro',
    scope: forwardLeftTotalityBody,
    sig: IOTA,
  })
  const forwardLeftTotalityOutput = onlyNewWire(
    publicBefore,
    publicForward.diagram,
    forwardLeftTotalityBody,
  )
  {
    const prior = publicForward.diagram
    publicForward.record('spawn residual A(a) totality result', {
      rule: 'atomSpawn',
      region: forwardLeftTotalityBody,
      wire: publicPlus,
    })
    const node = onlyNewNode(
      prior,
      publicForward.diagram,
      forwardLeftTotalityBody,
    )
    for (const [index, wire] of [
      [0, forwardLeft!],
      [1, forwardLeftTotalityInput],
      [2, forwardLeftTotalityOutput],
    ] as const) {
      publicForward.record(
        'attach residual A(a) totality argument ' + index,
        {
          rule: 'wireJoin',
          input: {
            kind: 'iota',
            a: wire,
            b: endpointWire(publicForward.diagram, node, 'arg', index),
          },
        },
      )
    }
  }

  publicBefore = publicForward.diagram
  publicForward.record('introduce temporary A(b) transport', {
    rule: 'vacuousIntro',
    scope: publicClaimAntecedent,
    sig: relSig([]),
  })
  const temporaryRightTransport = onlyNewWire(
    publicBefore,
    publicForward.diagram,
    publicClaimAntecedent,
  )
  publicBefore = publicForward.diagram
  publicForward.record('assert temporary A(b) transport', {
    rule: 'atomSpawn',
    region: publicClaimAntecedent,
    wire: temporaryRightTransport,
  })
  onlyNewNode(
    publicBefore,
    publicForward.diagram,
    publicClaimAntecedent,
  )
  publicForward.recordRelationJoin('ground exact residual A(b) transport', {
    wire: temporaryRightTransport,
      content: associativityTransportContent(),
      parameters: [publicForwardRight!, publicPlus],
  })
  const publicBackward = new PrimitiveStepRecorder(
    statements.plusAssoc.diagram,
    context,
    'backward',
  )
  const backwardPrimitiveScope = exactOne(
    directCuts(publicBackward.diagram, publicBackward.diagram.root),
    'backward public primitive scope',
  )
  const backwardPrimitiveBody = exactOne(
    directCuts(publicBackward.diagram, backwardPrimitiveScope),
    'backward public primitive body',
  )
  const backwardHypotheses = exactOne(
    directCuts(publicBackward.diagram, backwardPrimitiveBody),
    'backward public hypotheses',
  )
  const backwardConclusion = exactOne(
    directCuts(publicBackward.diagram, backwardHypotheses).filter((region) =>
      scopedWires(publicBackward.diagram, region).length === 0),
    'backward public conclusion',
  )
  const backwardClaimScope = exactOne(
    directCuts(publicBackward.diagram, backwardConclusion),
    'backward public claim scope',
  )
  const backwardClaimBody = exactOne(
    directCuts(publicBackward.diagram, backwardClaimScope),
    'backward public claim body',
  )
  const backwardClaimAntecedent = exactOne(
    directCuts(publicBackward.diagram, backwardClaimBody),
    'backward public claim antecedent',
  )
  const backwardZero = relationWire(
    publicBackward.diagram,
    backwardPrimitiveScope,
    UNARY,
  )
  const backwardSuccessor = relationWire(
    publicBackward.diagram,
    backwardPrimitiveScope,
    BINARY,
  )
  const backwardPlus = relationWire(
    publicBackward.diagram,
    backwardPrimitiveScope,
    TERNARY,
  )
  const citeSupport = (
    name: 'associativityCarrierBase' | 'associativityCarrierHereditary',
    scopedCount: 1 | 2,
  ) => {
    const beforeCitation = publicBackward.diagram
    publicBackward.record('cite ' + name + ' in public claim', {
      rule: 'theorem',
      name,
      direction: 'forward',
      at: {
        sel: {
          region: backwardClaimAntecedent,
          regions: [],
          nodes: [],
          wires: [],
        },
        args: [],
      },
    })
    const scope = onlyNewCut(
      beforeCitation,
      publicBackward.diagram,
      backwardClaimAntecedent,
    )
    const body = exactOne(
      directCuts(publicBackward.diagram, scope),
      name + ' primitive body',
    )
    const citedHypotheses = exactOne(
      directCuts(publicBackward.diagram, body),
      name + ' hypotheses',
    )
    const citedConclusion = exactOne(
      directCuts(publicBackward.diagram, citedHypotheses).filter((region) =>
        scopedWires(publicBackward.diagram, region).length === 0),
      name + ' conclusion',
    )
    const citedResult = exactOne(
      directCuts(publicBackward.diagram, citedConclusion).filter((region) =>
        scopedWires(publicBackward.diagram, region).length === scopedCount),
      name + ' direct result',
    )
    const primitiveSpecializations = name === 'associativityCarrierBase'
      ? [
          [
            backwardZero,
            relationWire(publicBackward.diagram, scope, UNARY),
            UNARY,
          ],
          [
            backwardPlus,
            relationWire(publicBackward.diagram, scope, TERNARY),
            TERNARY,
          ],
        ] as const
      : [
          [
            backwardSuccessor,
            relationWire(publicBackward.diagram, scope, BINARY),
            BINARY,
          ],
          [
            backwardPlus,
            relationWire(publicBackward.diagram, scope, TERNARY),
            TERNARY,
          ],
        ] as const
    for (const [outer, inner, signature] of primitiveSpecializations) {
      publicBackward.recordRelationJoin('specialize ' + name + ' primitive', {
    wire: inner,
          content: relationApplicationContent(signature),
          parameters: [outer],
  })
    }
    for (const citedHypothesis of directCuts(
      publicBackward.diagram,
      citedHypotheses,
    ).filter((region) => region !== citedConclusion)) {
      const sel = {
        region: citedHypotheses,
        regions: [citedHypothesis],
        nodes: [],
        wires: [],
      } as const
      const evidence = findDeiterationEvidence(
        publicBackward.diagram,
        sel,
        4096,
      )
      publicBackward.record('discharge ' + name + ' hypothesis', {
        rule: 'deiteration',
        sel,
        justifier: evidence.justifier,
        certificate: evidence.certificate,
        retargets: [],
      })
    }
    publicBackward.record('expose ' + name + ' conclusion', {
      rule: 'doubleCutElim',
      region: citedHypotheses,
    })
    publicBackward.record('remove ' + name + ' primitive scope', {
      rule: 'doubleCutElim',
      region: scope,
    })
    return citedResult
  }

  const exposedBackwardBase = citeSupport(
    'associativityCarrierBase',
    1,
  )
  const exposedBackwardClosure = citeSupport(
    'associativityCarrierHereditary',
    2,
  )
  let backwardBefore = publicBackward.diagram
  publicBackward.record('copy exact carrier base for Nat(b)', {
    rule: 'iteration',
    sel: {
      region: backwardClaimAntecedent,
      regions: [exposedBackwardBase],
      nodes: [],
      wires: [],
    },
    target: backwardClaimAntecedent,
    retargets: [],
  })
  const secondBackwardBase = onlyNewCut(
    backwardBefore,
    publicBackward.diagram,
    backwardClaimAntecedent,
  )
  const backwardClaimVariables = scopedWires(
    publicBackward.diagram,
    backwardClaimScope,
  )
  const left = backwardClaimVariables[0]!
  const leftNat = exactOne(
    directNodes(
      publicBackward.diagram,
      backwardClaimAntecedent,
    ).filter((node) =>
      publicBackward.diagram.nodes[node]!.kind === 'ref'
      && publicBackward.diagram.nodes[node]!.defId === 'nat'
      && endpointWire(publicBackward.diagram, node, 'arg', 2) === left),
    'public Nat(a)',
  )
  backwardBefore = publicBackward.diagram
  publicBackward.record('unfold public Nat(a)', {
    rule: 'unfold',
    nodeId: leftNat,
  })
  const leftPropertyScope = onlyNewCut(
    backwardBefore,
    publicBackward.diagram,
    backwardClaimAntecedent,
  )
  const leftPropertyBody = exactOne(
    directCuts(publicBackward.diagram, leftPropertyScope),
    'Nat(a) property body',
  )
  const leftProperty = relationWire(
    publicBackward.diagram,
    leftPropertyScope,
    UNARY,
  )
  publicBackward.recordRelationJoin('ground public Nat(a) directly to exact A', {
    wire: leftProperty,
      content: associativityCarrierContent(),
      parameters: [backwardPlus],
  })
  const leftHereditary = exactOne(
    directCuts(publicBackward.diagram, leftPropertyBody),
    'Nat(a) hereditary implication',
  )
  const leftNestedBase = exactOne(
    directCuts(publicBackward.diagram, leftHereditary).filter((region) =>
      scopedWires(publicBackward.diagram, region).length === 1),
    'Nat(a) nested base',
  )
  const leftNestedClosure = exactOne(
    directCuts(publicBackward.diagram, leftHereditary).filter((region) =>
      scopedWires(publicBackward.diagram, region).length === 2),
    'Nat(a) nested closure',
  )
  let leftBaseSourceUsed: string | undefined
  let rightBaseSourceUsed: string | undefined
  for (const [label, region, source] of [
    ['base', leftNestedBase, exposedBackwardBase],
    ['closure', leftNestedClosure, exposedBackwardClosure],
  ] as const) {
    const sel = {
      region: leftHereditary,
      regions: [region],
      nodes: [],
      wires: [],
    } as const
    const evidence = findDeiterationEvidence(
      publicBackward.diagram,
      sel,
      4096,
    )
    if (label === 'base') {
      leftBaseSourceUsed = evidence.justifier.regions[0]
      if (
        leftBaseSourceUsed !== exposedBackwardBase
        && leftBaseSourceUsed !== secondBackwardBase
      ) throw new Error('Nat(a) base did not use either exposed Base copy')
    } else if (!evidence.justifier.regions.includes(source)) {
      throw new Error('Nat(a) closure did not use exposed support')
    }
    publicBackward.record('discharge Nat(a) ' + label, {
      rule: 'deiteration',
      sel,
      justifier: evidence.justifier,
      certificate: evidence.certificate,
      retargets: [],
    })
  }
  publicBackward.record('expose inherited A(a)', {
    rule: 'doubleCutElim',
    region: leftHereditary,
  })
  publicBackward.record('remove grounded Nat(a) property scope', {
    rule: 'doubleCutElim',
    region: leftPropertyScope,
  })
  const inheritedLeftComponents = directCuts(
    publicBackward.diagram,
    backwardClaimAntecedent,
  ).filter((region) =>
    scopedWires(publicBackward.diagram, region).length === 1
    || scopedWires(publicBackward.diagram, region).length === 4)
  const right = backwardClaimVariables[1]!
  const rightNat = exactOne(
    directNodes(
      publicBackward.diagram,
      backwardClaimAntecedent,
    ).filter((node) =>
      publicBackward.diagram.nodes[node]!.kind === 'ref'
      && publicBackward.diagram.nodes[node]!.defId === 'nat'
      && endpointWire(publicBackward.diagram, node, 'arg', 2) === right),
    'public Nat(b)',
  )
  backwardBefore = publicBackward.diagram
  publicBackward.record('unfold public Nat(b)', {
    rule: 'unfold',
    nodeId: rightNat,
  })
  const rightPropertyScope = onlyNewCut(
    backwardBefore,
    publicBackward.diagram,
    backwardClaimAntecedent,
  )
  const rightPropertyBody = exactOne(
    directCuts(publicBackward.diagram, rightPropertyScope),
    'Nat(b) property body',
  )
  const rightProperty = relationWire(
    publicBackward.diagram,
    rightPropertyScope,
    UNARY,
  )
  publicBackward.recordRelationJoin('ground public Nat(b) directly to exact A', {
    wire: rightProperty,
      content: associativityCarrierContent(),
      parameters: [backwardPlus],
  })
  const rightHereditary = exactOne(
    directCuts(publicBackward.diagram, rightPropertyBody),
    'Nat(b) hereditary implication',
  )
  const rightNestedBase = exactOne(
    directCuts(publicBackward.diagram, rightHereditary).filter((region) =>
      scopedWires(publicBackward.diagram, region).length === 1),
    'Nat(b) nested base',
  )
  const rightNestedClosure = exactOne(
    directCuts(publicBackward.diagram, rightHereditary).filter((region) =>
      scopedWires(publicBackward.diagram, region).length === 2),
    'Nat(b) nested closure',
  )
  const rightCarrierResult = exactOne(
    directCuts(publicBackward.diagram, rightHereditary).filter((region) =>
      scopedWires(publicBackward.diagram, region).length === 0),
    'Nat(b) exact carrier result',
  )
  const inheritedRightTotality = exactOne(
    directCuts(publicBackward.diagram, rightCarrierResult).filter((region) =>
      scopedWires(publicBackward.diagram, region).length === 1),
    'inherited A(b) totality',
  )
  const inheritedRightTransport = exactOne(
    directCuts(publicBackward.diagram, rightCarrierResult).filter((region) =>
      scopedWires(publicBackward.diagram, region).length === 4),
    'inherited A(b) transport',
  )
  for (const [label, region, source] of [
    ['base', rightNestedBase, secondBackwardBase],
    ['closure', rightNestedClosure, exposedBackwardClosure],
  ] as const) {
    const sel = {
      region: rightHereditary,
      regions: [region],
      nodes: [],
      wires: [],
    } as const
    const evidence = findDeiterationEvidence(
      publicBackward.diagram,
      sel,
      4096,
    )
    if (label === 'base') {
      rightBaseSourceUsed = evidence.justifier.regions[0]
      if (
        rightBaseSourceUsed !== exposedBackwardBase
        && rightBaseSourceUsed !== secondBackwardBase
      ) throw new Error('Nat(b) base did not use either exposed Base copy')
    } else if (!evidence.justifier.regions.includes(source)) {
      throw new Error('Nat(b) closure did not use exposed support')
    }
    publicBackward.record('discharge Nat(b) ' + label, {
      rule: 'deiteration',
      sel,
      justifier: evidence.justifier,
      certificate: evidence.certificate,
      retargets: [],
    })
  }
  publicBackward.record('expose inherited A(b)', {
    rule: 'doubleCutElim',
    region: rightHereditary,
  })
  publicBackward.record('remove grounded Nat(b) property scope', {
    rule: 'doubleCutElim',
    region: rightPropertyScope,
  })
  const third = backwardClaimVariables[2]!
  const firstSum = backwardClaimVariables[3]!
  const publicOutput = backwardClaimVariables[4]!
  const publicPremises = directNodes(
    publicBackward.diagram,
    backwardClaimAntecedent,
  ).filter((node) =>
    publicBackward.diagram.nodes[node]!.kind === 'atom'
    && endpointWire(publicBackward.diagram, node, 'head') === backwardPlus)
  if (publicPremises.length !== 2) {
    throw new Error('expected exactly two original public Plus premises')
  }
  const publicFirstPremise = exactOne(
    publicPremises.filter((node) =>
      endpointWire(publicBackward.diagram, node, 'arg', 0) === left),
    'public Plus(a,b,t)',
  )
  const publicSecondPremise = exactOne(
    publicPremises.filter((node) => node !== publicFirstPremise),
    'public Plus(t,c,o)',
  )
  const rightTotalityInput = exactOne(
    scopedWires(publicBackward.diagram, inheritedRightTotality),
    'A(b) totality input',
  )
  publicBackward.record('specialize A(b) totality at c', {
    rule: 'wireJoin',
    input: {
      kind: 'iota',
      a: third,
      b: rightTotalityInput,
    },
  })
  const rightTotalityBody = exactOne(
    directCuts(publicBackward.diagram, inheritedRightTotality),
    'A(b) totality body',
  )
  const derivedInner = exactOne(
    directNodes(publicBackward.diagram, rightTotalityBody).filter((node) =>
      endpointWire(publicBackward.diagram, node, 'head') === backwardPlus),
    'derived Plus(b,c,u)',
  )
  const innerSum = endpointWire(
    publicBackward.diagram,
    derivedInner,
    'arg',
    2,
  )
  publicBackward.record('expose A(b) totality witness', {
    rule: 'doubleCutElim',
    region: inheritedRightTotality,
  })

  const leftTransport = exactOne(
    directCuts(publicBackward.diagram, backwardClaimAntecedent)
      .filter((region) =>
        scopedWires(publicBackward.diagram, region).length === 4
        && region !== inheritedRightTransport)
      .filter((region) => {
        const body = directCuts(publicBackward.diagram, region)[0]
        const antecedent = body === undefined
          ? undefined
          : directCuts(publicBackward.diagram, body)[0]
        return antecedent !== undefined
          && directNodes(publicBackward.diagram, antecedent).some((node) =>
            publicBackward.diagram.nodes[node]!.kind === 'atom'
            && endpointWire(publicBackward.diagram, node, 'head')
              === backwardPlus
            && endpointWire(publicBackward.diagram, node, 'arg', 0) === left)
      }),
    'inherited A(a) transport',
  )
  const leftTransportVariables = scopedWires(
    publicBackward.diagram,
    leftTransport,
  )
  if (leftTransportVariables.length !== 4) {
    throw new Error('expected four A(a) transport variables')
  }
  for (const [label, outer, inner] of [
    ['right', right, leftTransportVariables[0]!],
    ['third', third, leftTransportVariables[1]!],
    ['first sum', firstSum, leftTransportVariables[2]!],
    ['inner sum', innerSum, leftTransportVariables[3]!],
  ] as const) {
    publicBackward.record('specialize A(a) transport ' + label, {
      rule: 'wireJoin',
      input: {
        kind: 'iota',
        a: outer,
        b: inner,
      },
    })
  }
  const leftTransportBody = exactOne(
    directCuts(publicBackward.diagram, leftTransport),
    'A(a) transport body',
  )
  const leftTransportAntecedent = exactOne(
    directCuts(publicBackward.diagram, leftTransportBody),
    'A(a) transport antecedent',
  )
  const leftTransportConsequent = exactOne(
    directCuts(publicBackward.diagram, leftTransportAntecedent),
    'A(a) transport consequent',
  )
  const leftTransportPremises = directNodes(
    publicBackward.diagram,
    leftTransportAntecedent,
  ).filter((node) =>
    endpointWire(publicBackward.diagram, node, 'head') === backwardPlus)
  const transportFirstPremise = exactOne(
    leftTransportPremises.filter((node) =>
      endpointWire(publicBackward.diagram, node, 'arg', 0) === left),
    'A(a) first transport premise',
  )
  const transportInnerPremise = exactOne(
    leftTransportPremises.filter((node) => node !== transportFirstPremise),
    'A(a) inner transport premise',
  )
  const leftTransportResults = directNodes(
    publicBackward.diagram,
    leftTransportConsequent,
  ).filter((node) =>
    endpointWire(publicBackward.diagram, node, 'head') === backwardPlus)
  const transportOuterResult = exactOne(
    leftTransportResults.filter((node) =>
      endpointWire(publicBackward.diagram, node, 'arg', 0) === left),
    'A(a) outer transport result',
  )
  const transportFirstResult = exactOne(
    leftTransportResults.filter((node) => node !== transportOuterResult),
    'A(a) first-sum transport result',
  )
  const transportOutput = endpointWire(
    publicBackward.diagram,
    transportOuterResult,
    'arg',
    2,
  )
  publicBackward.record(
    'discharge A(a) first transport premise',
    deiterationStep(
      publicBackward.diagram,
      leftTransportAntecedent,
      transportFirstPremise,
    ),
  )
  publicBackward.record(
    'discharge A(a) inner transport premise',
    deiterationStep(
      publicBackward.diagram,
      leftTransportAntecedent,
      transportInnerPremise,
    ),
  )
  publicBackward.record('expose A(a) transport results', {
    rule: 'doubleCutElim',
    region: leftTransportAntecedent,
  })
  publicBackward.record('remove specialized A(a) transport scope', {
    rule: 'doubleCutElim',
    region: leftTransport,
  })
  const publicAdditionFunctional = exactOne(
    directCuts(publicBackward.diagram, backwardHypotheses).filter((region) =>
      scopedWires(publicBackward.diagram, region).length === 4),
    'public plusSingleValued hypothesis',
  )
  backwardBefore = publicBackward.diagram
  publicBackward.record('copy addition functionality for transport output', {
    rule: 'iteration',
    sel: {
      region: backwardHypotheses,
      regions: [publicAdditionFunctional],
      nodes: [],
      wires: [],
    },
    target: backwardClaimAntecedent,
    retargets: [],
  })
  const copiedOutputFunctional = onlyNewCut(
    backwardBefore,
    publicBackward.diagram,
    backwardClaimAntecedent,
  )
  const copiedOutputFunctionalBody = exactOne(
    directCuts(publicBackward.diagram, copiedOutputFunctional),
    'output functionality body',
  )
  const copiedOutputFunctionalAntecedent = exactOne(
    directCuts(publicBackward.diagram, copiedOutputFunctionalBody),
    'output functionality antecedent',
  )
  const copiedOutputFunctionalConsequent = exactOne(
    directCuts(publicBackward.diagram, copiedOutputFunctionalAntecedent),
    'output functionality consequent',
  )
  const copiedOutputFunctionalPremises = directNodes(
    publicBackward.diagram,
    copiedOutputFunctionalAntecedent,
  ).filter((node) =>
    endpointWire(publicBackward.diagram, node, 'head') === backwardPlus)
  if (copiedOutputFunctionalPremises.length !== 2) {
    throw new Error('expected two output-functionality premises')
  }
  const [
    copiedOutputFunctionalFirst,
    copiedOutputFunctionalSecond,
  ] = copiedOutputFunctionalPremises
  for (const [label, outer, inner] of [
    [
      'left',
      firstSum,
      endpointWire(
        publicBackward.diagram,
        copiedOutputFunctionalFirst!,
        'arg',
        0,
      ),
    ],
    [
      'right',
      third,
      endpointWire(
        publicBackward.diagram,
        copiedOutputFunctionalFirst!,
        'arg',
        1,
      ),
    ],
    [
      'public output',
      publicOutput,
      endpointWire(
        publicBackward.diagram,
        copiedOutputFunctionalFirst!,
        'arg',
        2,
      ),
    ],
    [
      'transport output',
      transportOutput,
      endpointWire(
        publicBackward.diagram,
        copiedOutputFunctionalSecond!,
        'arg',
        2,
      ),
    ],
  ] as const) {
    publicBackward.record('specialize output functionality ' + label, {
      rule: 'wireJoin',
      input: { kind: 'iota', a: outer, b: inner },
    })
  }
  for (const premise of copiedOutputFunctionalPremises) {
    publicBackward.record(
      'discharge output functionality premise',
      deiterationStep(
        publicBackward.diagram,
        copiedOutputFunctionalAntecedent,
        premise,
      ),
    )
  }
  const outputIdentity = exactOne(
    directNodes(publicBackward.diagram, copiedOutputFunctionalConsequent),
    'public/transport output identity',
  )
  publicBackward.record('expose public/transport output identity', {
    rule: 'doubleCutElim',
    region: copiedOutputFunctionalAntecedent,
  })
  publicBackward.record('finish output functionality specialization', {
    rule: 'doubleCutElim',
    region: copiedOutputFunctional,
  })
  const outerSelection = {
    region: backwardClaimAntecedent,
    regions: [],
    nodes: [transportOuterResult],
    wires: [],
  } as const
  const outerOutputBoundary = extractSubgraph(
    publicBackward.diagram,
    outerSelection,
  ).attachments.indexOf(transportOutput)
  if (outerOutputBoundary < 0) {
    throw new Error('transport outer result lost its output boundary')
  }
  backwardBefore = publicBackward.diagram
  publicBackward.record('retarget A(a) outer result to public output', {
    rule: 'iteration',
    sel: outerSelection,
    target: backwardClaimAntecedent,
    retargets: [{
      boundary: outerOutputBoundary,
      identity: outputIdentity,
      from: transportOutput,
      to: publicOutput,
    }],
  })
  const retargetedOuterResult = onlyNewNode(
    backwardBefore,
    publicBackward.diagram,
    backwardClaimAntecedent,
  )

  void inheritedLeftComponents
  void publicSecondPremise
  void transportFirstResult
  void retargetedOuterResult
  return {
    name: 'plusAssoc',
    lhs: publicLhs,
    rhs: statements.plusAssoc,
    actions: publicForward.actions,
    backActions: publicBackward.actions,
  }
}

export function buildArithmeticAssociativityTheorems(
  relations: Theory['relations'],
  prefix: readonly Theorem[],
  statements: ArithmeticStatements,
): readonly Theorem[] {
  let context = verifyTheory({ relations, theorems: prefix })
  const base = associativityCarrierBase(statements, context)
  context = registerTheorem(context, base)
  const hereditary = associativityCarrierHereditary(statements, context)
  context = registerTheorem(context, hereditary)
  const associativity = plusAssoc(statements, context)
  context = registerTheorem(context, associativity)
  void context
  return Object.freeze([base, hereditary, associativity])
}
