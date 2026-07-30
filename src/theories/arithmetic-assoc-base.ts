import type { ProofContext } from '../kernel/proof/context'
import type { Theorem } from '../kernel/proof/theorem'
import { extractSubgraph } from '../kernel/diagram/subgraph/extract'
import { IOTA, relSig } from '../kernel/diagram/sig'
import {
  TERNARY,
  UNARY,
  deiterationSelectionStep,
  deiterationStep,
  directCuts,
  directNodes,
  endpointWire,
  exactOne,
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
import type { ArithmeticStatements } from './statements'

function exactHypothesesContent() {
  let graph = emptyGraph()
  const zero = declareWire(graph, graph.root, UNARY)
  graph = zero.graph
  const plus = declareWire(graph, graph.root, TERNARY)
  graph = plus.graph

  const baseVariables = quantifierScope(
    graph,
    graph.root,
    'forall',
    [IOTA, IOTA],
  )
  graph = baseVariables.graph
  const [zeroValue, right] = baseVariables.value.variables
  const baseClaim = implication(graph, baseVariables.value.body)
  graph = baseClaim.graph
  graph = atom(
    graph,
    baseClaim.value.antecedent,
    zero.value,
    [zeroValue!],
  ).graph
  graph = atom(
    graph,
    baseClaim.value.consequent,
    plus.value,
    [zeroValue!, right!, right!],
  ).graph

  const functionalVariables = quantifierScope(
    graph,
    graph.root,
    'forall',
    [IOTA, IOTA, IOTA, IOTA],
  )
  graph = functionalVariables.graph
  const [left, functionalRight, first, second] =
    functionalVariables.value.variables
  const functionalClaim = implication(
    graph,
    functionalVariables.value.body,
  )
  graph = functionalClaim.graph
  graph = atom(
    graph,
    functionalClaim.value.antecedent,
    plus.value,
    [left!, functionalRight!, first!],
  ).graph
  graph = atom(
    graph,
    functionalClaim.value.antecedent,
    plus.value,
    [left!, functionalRight!, second!],
  ).graph
  graph = identity(
    graph,
    functionalClaim.value.consequent,
    [first!, second!],
  ).graph

  return finishDiagramWithBoundary(graph, [zero.value, plus.value])
}

export function associativityCarrierBase(
  statements: ArithmeticStatements,
  context: ProofContext,
): Theorem {
  const lhs = finishDiagramWithBoundary(emptyGraph(), [])
  const forward = new PrimitiveStepRecorder(lhs.diagram, context)
  let before = forward.diagram
  forward.record('open base-support primitive scope', {
    rule: 'doubleCutIntro',
    sel: { region: forward.diagram.root, regions: [], nodes: [], wires: [] },
  })
  const forwardPrimitiveScope = onlyNewCut(
    before,
    forward.diagram,
    forward.diagram.root,
  )
  const forwardPrimitiveBody = exactOne(
    directCuts(forward.diagram, forwardPrimitiveScope),
    'forward primitive body',
  )
  const relationsWires: string[] = []
  for (const [label, sig] of [
    ['zero', UNARY],
    ['addition', TERNARY],
  ] as const) {
    before = forward.diagram
    forward.record('introduce base-support ' + label + ' relation', {
      rule: 'vacuousIntro',
      scope: forwardPrimitiveScope,
      sig,
    })
    relationsWires.push(
      onlyNewWire(before, forward.diagram, forwardPrimitiveScope),
    )
  }
  const [forwardZero, forwardPlus] = relationsWires
  before = forward.diagram
  forward.record('open base-support standing implication', {
    rule: 'doubleCutIntro',
    sel: { region: forwardPrimitiveBody, regions: [], nodes: [], wires: [] },
  })
  const forwardHypotheses = onlyNewCut(
    before,
    forward.diagram,
    forwardPrimitiveBody,
  )
  const forwardConclusion = exactOne(
    directCuts(forward.diagram, forwardHypotheses),
    'forward conclusion',
  )
  before = forward.diagram
  forward.record('introduce temporary standing hypotheses', {
    rule: 'vacuousIntro',
    scope: forwardHypotheses,
    sig: relSig([]),
  })
  const temporaryHypotheses = onlyNewWire(
    before,
    forward.diagram,
    forwardHypotheses,
  )
  before = forward.diagram
  forward.record('assert temporary standing hypotheses', {
    rule: 'atomSpawn',
    region: forwardHypotheses,
    wire: temporaryHypotheses,
  })
  onlyNewNode(before, forward.diagram, forwardHypotheses)
  forward.recordRelationJoin('ground exact standing hypotheses', {
    wire: temporaryHypotheses,
      content: exactHypothesesContent(),
      parameters: [forwardZero!, forwardPlus!],
  })
  before = forward.diagram
  forward.record('open material base universal', {
    rule: 'doubleCutIntro',
    sel: { region: forwardConclusion, regions: [], nodes: [], wires: [] },
  })
  const forwardBase = onlyNewCut(before, forward.diagram, forwardConclusion)
  const forwardBaseBody = exactOne(
    directCuts(forward.diagram, forwardBase),
    'forward base body',
  )
  before = forward.diagram
  forward.record('introduce material base value', {
    rule: 'vacuousIntro',
    scope: forwardBase,
    sig: IOTA,
  })
  const forwardBaseValue = onlyNewWire(before, forward.diagram, forwardBase)
  before = forward.diagram
  forward.record('open material base implication', {
    rule: 'doubleCutIntro',
    sel: { region: forwardBaseBody, regions: [], nodes: [], wires: [] },
  })
  const forwardBaseAntecedent = onlyNewCut(
    before,
    forward.diagram,
    forwardBaseBody,
  )
  const forwardBaseConsequent = exactOne(
    directCuts(forward.diagram, forwardBaseAntecedent),
    'forward base consequent',
  )
  function spawn(
    region: string,
    head: string,
    args: readonly string[],
    label: string,
  ) {
    const prior = forward.diagram
    forward.record('spawn ' + label, { rule: 'atomSpawn', region, wire: head })
    const node = onlyNewNode(prior, forward.diagram, region)
    args.forEach((wire, index) => {
      forward.record('attach ' + label + ' argument ' + index, {
        rule: 'wireJoin',
        input: {
          a: wire,
          b: endpointWire(forward.diagram, node, 'arg', index),
        },
      })
    })
    return node
  }
  spawn(
    forwardBaseAntecedent,
    forwardZero!,
    [forwardBaseValue],
    'material base Zero',
  )
  spawn(
    forwardBaseAntecedent,
    forwardPlus!,
    [forwardBaseValue, forwardBaseValue, forwardBaseValue],
    'material base anchor',
  )
  before = forward.diagram
  forward.record('open material transport universal', {
    rule: 'doubleCutIntro',
    sel: {
      region: forwardBaseConsequent,
      regions: [],
      nodes: [],
      wires: [],
    },
  })
  const forwardTransport = onlyNewCut(
    before,
    forward.diagram,
    forwardBaseConsequent,
  )
  const forwardTransportBody = exactOne(
    directCuts(forward.diagram, forwardTransport),
    'forward transport body',
  )
  const transportVariables: string[] = []
  for (const label of ['right', 'third', 'first sum', 'inner sum']) {
    before = forward.diagram
    forward.record('introduce material transport ' + label, {
      rule: 'vacuousIntro',
      scope: forwardTransport,
      sig: IOTA,
    })
    transportVariables.push(
      onlyNewWire(before, forward.diagram, forwardTransport),
    )
  }
  const [forwardRight, forwardThird, forwardFirst, forwardInner] =
    transportVariables
  before = forward.diagram
  forward.record('open material transport implication', {
    rule: 'doubleCutIntro',
    sel: {
      region: forwardTransportBody,
      regions: [],
      nodes: [],
      wires: [],
    },
  })
  const forwardTransportAntecedent = onlyNewCut(
    before,
    forward.diagram,
    forwardTransportBody,
  )
  exactOne(
    directCuts(forward.diagram, forwardTransportAntecedent),
    'forward transport consequent',
  )
  spawn(
    forwardTransportAntecedent,
    forwardPlus!,
    [forwardBaseValue, forwardRight!, forwardFirst!],
    'material first premise',
  )
  spawn(
    forwardTransportAntecedent,
    forwardPlus!,
    [forwardRight!, forwardThird!, forwardInner!],
    'material inner premise',
  )
  spawn(
    forwardTransportAntecedent,
    forwardPlus!,
    [forwardBaseValue, forwardRight!, forwardRight!],
    'material right base',
  )
  spawn(
    forwardTransportAntecedent,
    forwardPlus!,
    [forwardBaseValue, forwardInner!, forwardInner!],
    'material inner base',
  )
  before = forward.diagram
  forward.record('insert material functionality identity', {
    rule: 'identityInsert',
    region: forwardTransportAntecedent,
    wires: [forwardFirst!, forwardRight!],
  })
  spawn(
    forwardTransportAntecedent,
    forwardPlus!,
    [forwardFirst!, forwardThird!, forwardInner!],
    'material transported inner',
  )

    const rhs = statements.associativityCarrierBase
  const backward = new PrimitiveStepRecorder(rhs.diagram, context, 'backward')
  const primitiveScope = exactOne(
    directCuts(backward.diagram, backward.diagram.root),
    'backward primitive scope',
  )
  const primitiveBody = exactOne(
    directCuts(backward.diagram, primitiveScope),
    'backward primitive body',
  )
  const hypotheses = exactOne(
    directCuts(backward.diagram, primitiveBody),
    'backward hypotheses',
  )
  const conclusion = exactOne(
    directCuts(backward.diagram, hypotheses).filter((region) =>
      scopedWires(backward.diagram, region).length === 0),
    'backward conclusion',
  )
  const nestedBase = exactOne(
    directCuts(backward.diagram, conclusion),
    'backward base',
  )
  const zero = scopedWires(backward.diagram, primitiveScope).find((wire) =>
    backward.diagram.wires[wire]!.sig.kind === 'rel'
    && backward.diagram.wires[wire]!.sig.args.length === 1)!
  const plus = scopedWires(backward.diagram, primitiveScope).find((wire) =>
    backward.diagram.wires[wire]!.sig.kind === 'rel'
    && backward.diagram.wires[wire]!.sig.args.length === 3)!

  const baseBody = exactOne(
    directCuts(backward.diagram, nestedBase),
    'inline base body',
  )
  const baseAntecedent = exactOne(
    directCuts(backward.diagram, baseBody),
    'inline base antecedent',
  )
  const baseConsequent = exactOne(
    directCuts(backward.diagram, baseAntecedent),
    'inline base consequent',
  )
  const baseValue = exactOne(
    scopedWires(backward.diagram, nestedBase),
    'inline base value',
  )
  const baseZero = exactOne(
    directNodes(backward.diagram, baseAntecedent).filter((node) =>
      endpointWire(backward.diagram, node, 'head') === zero),
    'inline base Zero',
  )
  const baseTotality = exactOne(
    directCuts(backward.diagram, baseConsequent).filter((region) =>
      scopedWires(backward.diagram, region).length === 1),
    'inline base totality',
  )
  const baseTotalityInput = exactOne(
    scopedWires(backward.diagram, baseTotality),
    'inline base totality input',
  )
  const baseTotalityBody = exactOne(
    directCuts(backward.diagram, baseTotality),
    'inline base totality body',
  )
  const baseTotalityGoal = exactOne(
    directNodes(backward.diagram, baseTotalityBody).filter((node) =>
      endpointWire(backward.diagram, node, 'head') === plus),
    'inline base totality goal',
  )
  const baseTotalityOutput = endpointWire(
    backward.diagram,
    baseTotalityGoal,
    'arg',
    2,
  )
  backward.record('choose inline-base totality witness', {
    rule: 'wireJoin',
    input: {
      a: baseTotalityInput,
      b: baseTotalityOutput,
    },
  })
  const additionBase = exactOne(
    directCuts(backward.diagram, hypotheses).filter((region) =>
      scopedWires(backward.diagram, region).length === 2),
    'plusBase hypothesis',
  )
  before = backward.diagram
  backward.record('copy addition base into inline carrier base', {
    rule: 'iteration',
    sel: {
      region: hypotheses,
      regions: [additionBase],
      nodes: [],
      wires: [],
    },
    target: baseAntecedent,
    retargets: [],
  })
  const copiedAdditionBase = onlyNewCut(
    before,
    backward.diagram,
    baseAntecedent,
  )
  const copiedAdditionBaseBody = exactOne(
    directCuts(backward.diagram, copiedAdditionBase),
    'copied addition-base body',
  )
  const copiedAdditionBaseAntecedent = exactOne(
    directCuts(backward.diagram, copiedAdditionBaseBody),
    'copied addition-base antecedent',
  )
  const copiedAdditionBaseConsequent = exactOne(
    directCuts(backward.diagram, copiedAdditionBaseAntecedent),
    'copied addition-base consequent',
  )
  const copiedAdditionBaseZero = exactOne(
    directNodes(backward.diagram, copiedAdditionBaseAntecedent).filter((node) =>
      endpointWire(backward.diagram, node, 'head') === zero),
    'copied addition-base Zero',
  )
  const copiedAdditionBaseResult = exactOne(
    directNodes(backward.diagram, copiedAdditionBaseConsequent).filter((node) =>
      endpointWire(backward.diagram, node, 'head') === plus),
    'copied addition-base result',
  )
  const copiedAdditionBaseRight = endpointWire(
    backward.diagram,
    copiedAdditionBaseResult,
    'arg',
    1,
  )
  backward.record('specialize copied addition-base zero', {
    rule: 'wireJoin',
    input: {
      a: baseValue,
      b: endpointWire(backward.diagram, copiedAdditionBaseZero, 'arg', 0),
    },
  })
  backward.record(
    'discharge copied addition-base Zero',
    deiterationStep(
      backward.diagram,
      copiedAdditionBaseAntecedent,
      copiedAdditionBaseZero,
    ),
  )
  backward.record('expose copied addition-base result', {
    rule: 'doubleCutElim',
    region: copiedAdditionBaseAntecedent,
  })
  backward.record(
    'discharge inline carrier totality obligation',
    deiterationSelectionStep(
      backward.diagram,
      {
        region: baseConsequent,
        regions: [baseTotality],
        nodes: [],
        wires: [],
      },
    ),
  )
  backward.record('collapse residual addition-base input', {
    rule: 'wireJoin',
    input: {
      a: baseValue,
      b: copiedAdditionBaseRight,
    },
  })
  backward.record('expose collapsed addition-base witness', {
    rule: 'doubleCutElim',
    region: copiedAdditionBase,
  })
  const baseTransport = exactOne(
    directCuts(backward.diagram, baseConsequent).filter((region) =>
      scopedWires(backward.diagram, region).length === 4),
    'inline base transport',
  )
  const baseTransportBody = exactOne(
    directCuts(backward.diagram, baseTransport),
    'inline base transport body',
  )
  const baseTransportAntecedent = exactOne(
    directCuts(backward.diagram, baseTransportBody),
    'inline base transport antecedent',
  )
  const baseTransportConsequent = exactOne(
    directCuts(backward.diagram, baseTransportAntecedent),
    'inline base transport consequent',
  )
  const baseTransportPremises = directNodes(
    backward.diagram,
    baseTransportAntecedent,
  ).filter((node) => endpointWire(backward.diagram, node, 'head') === plus)
  const baseTransportFirst = exactOne(
    baseTransportPremises.filter((node) =>
      endpointWire(backward.diagram, node, 'arg', 0) === baseValue),
    'inline base first transport premise',
  )
  const baseTransportInner = exactOne(
    baseTransportPremises.filter((node) => node !== baseTransportFirst),
    'inline base inner transport premise',
  )
  const baseTransportRight = endpointWire(
    backward.diagram,
    baseTransportFirst,
    'arg',
    1,
  )
  const baseTransportFirstSum = endpointWire(
    backward.diagram,
    baseTransportFirst,
    'arg',
    2,
  )
  const baseTransportInnerSum = endpointWire(
    backward.diagram,
    baseTransportInner,
    'arg',
    2,
  )
  const baseTransportGoals = directNodes(
    backward.diagram,
    baseTransportConsequent,
  ).filter((node) => endpointWire(backward.diagram, node, 'head') === plus)
  const baseTransportOuterGoal = exactOne(
    baseTransportGoals.filter((node) =>
      endpointWire(backward.diagram, node, 'arg', 0) === baseValue),
    'inline base outer transport goal',
  )
  const baseTransportFirstGoal = exactOne(
    baseTransportGoals.filter((node) => node !== baseTransportOuterGoal),
    'inline base first-sum transport goal',
  )
  const baseTransportOutput = endpointWire(
    backward.diagram,
    baseTransportOuterGoal,
    'arg',
    2,
  )
  backward.record('choose inline-base transport output', {
    rule: 'wireJoin',
    input: {
      a: baseTransportInnerSum,
      b: baseTransportOutput,
    },
  })
  const deriveBaseAddition = (
    right: string,
    label: string,
  ) => {
    const prior = backward.diagram
    backward.record(`copy addition base for ${label}`, {
      rule: 'iteration',
      sel: {
        region: hypotheses,
        regions: [additionBase],
        nodes: [],
        wires: [],
      },
      target: baseTransportAntecedent,
      retargets: [],
    })
    const scope = onlyNewCut(
      prior,
      backward.diagram,
      baseTransportAntecedent,
    )
    const body = exactOne(directCuts(backward.diagram, scope), `${label} body`)
    const antecedent = exactOne(
      directCuts(backward.diagram, body),
      `${label} antecedent`,
    )
    const consequent = exactOne(
      directCuts(backward.diagram, antecedent),
      `${label} consequent`,
    )
    const zeroPremise = exactOne(
      directNodes(backward.diagram, antecedent).filter((node) =>
        endpointWire(backward.diagram, node, 'head') === zero),
      `${label} Zero`,
    )
    const result = exactOne(
      directNodes(backward.diagram, consequent).filter((node) =>
        endpointWire(backward.diagram, node, 'head') === plus),
      `${label} Plus`,
    )
    backward.record(`specialize ${label} zero`, {
      rule: 'wireJoin',
      input: {
        a: baseValue,
        b: endpointWire(backward.diagram, zeroPremise, 'arg', 0),
      },
    })
    backward.record(`specialize ${label} right`, {
      rule: 'wireJoin',
      input: {
        a: right,
        b: endpointWire(backward.diagram, result, 'arg', 1),
      },
    })
    backward.record(
      `discharge ${label} Zero`,
      deiterationStep(backward.diagram, antecedent, zeroPremise),
    )
    backward.record(`expose ${label} result`, {
      rule: 'doubleCutElim',
      region: antecedent,
    })
    backward.record(`finish ${label} specialization`, {
      rule: 'doubleCutElim',
      region: scope,
    })
    return result
  }
  const baseAtRight = deriveBaseAddition(
    baseTransportRight,
    'inline-base right',
  )
  const baseAtInner = deriveBaseAddition(
    baseTransportInnerSum,
    'inline-base inner',
  )
  const additionFunctional = exactOne(
    directCuts(backward.diagram, hypotheses).filter((region) =>
      scopedWires(backward.diagram, region).length === 4),
    'plusSingleValued hypothesis',
  )
  before = backward.diagram
  backward.record('copy addition functionality into inline base transport', {
    rule: 'iteration',
    sel: {
      region: hypotheses,
      regions: [additionFunctional],
      nodes: [],
      wires: [],
    },
    target: baseTransportAntecedent,
    retargets: [],
  })
  const copiedFunctional = onlyNewCut(
    before,
    backward.diagram,
    baseTransportAntecedent,
  )
  const copiedFunctionalBody = exactOne(
    directCuts(backward.diagram, copiedFunctional),
    'inline-base functionality body',
  )
  const copiedFunctionalAntecedent = exactOne(
    directCuts(backward.diagram, copiedFunctionalBody),
    'inline-base functionality antecedent',
  )
  const copiedFunctionalConsequent = exactOne(
    directCuts(backward.diagram, copiedFunctionalAntecedent),
    'inline-base functionality consequent',
  )
  const copiedFunctionalPluses = directNodes(
    backward.diagram,
    copiedFunctionalAntecedent,
  ).filter((node) => endpointWire(backward.diagram, node, 'head') === plus)
  if (copiedFunctionalPluses.length !== 2) {
    throw new Error('expected two inline-base functionality premises')
  }
  const copiedFunctionalFirst = copiedFunctionalPluses[0]!
  const copiedFunctionalSecond = copiedFunctionalPluses[1]!
  for (const [target, variable] of [
    [baseValue, endpointWire(backward.diagram, copiedFunctionalFirst, 'arg', 0)],
    [baseTransportRight, endpointWire(backward.diagram, copiedFunctionalFirst, 'arg', 1)],
    [baseTransportFirstSum, endpointWire(backward.diagram, copiedFunctionalFirst, 'arg', 2)],
    [baseTransportRight, endpointWire(backward.diagram, copiedFunctionalSecond, 'arg', 2)],
  ] as const) {
    backward.record('specialize inline-base functionality', {
      rule: 'wireJoin',
      input: { a: target, b: variable },
    })
  }
  backward.record(
    'discharge inline-base functional original result',
    deiterationStep(
      backward.diagram,
      copiedFunctionalAntecedent,
      copiedFunctionalFirst,
    ),
  )
  backward.record(
    'discharge inline-base functional canonical result',
    deiterationStep(
      backward.diagram,
      copiedFunctionalAntecedent,
      copiedFunctionalSecond,
    ),
  )
  const baseOutputIdentity = exactOne(
    directNodes(backward.diagram, copiedFunctionalConsequent),
    'inline-base functionality identity',
  )
  backward.record('expose inline-base output identity', {
    rule: 'doubleCutElim',
    region: copiedFunctionalAntecedent,
  })
  backward.record('finish inline-base functionality', {
    rule: 'doubleCutElim',
    region: copiedFunctional,
  })
  const innerSelection = {
    region: baseTransportAntecedent,
    regions: [],
    nodes: [baseTransportInner],
    wires: [],
  } as const
  const innerBoundary = extractSubgraph(
    backward.diagram,
    innerSelection,
  ).attachments.indexOf(baseTransportRight)
  if (innerBoundary < 0) throw new Error('inner premise lost right boundary')
  before = backward.diagram
  backward.record('retarget inline-base inner premise', {
    rule: 'iteration',
    sel: innerSelection,
    target: baseTransportAntecedent,
    retargets: [{
      boundary: innerBoundary,
      identity: baseOutputIdentity,
      from: baseTransportRight,
      to: baseTransportFirstSum,
    }],
  })
  const transportedInner = onlyNewNode(
    before,
    backward.diagram,
    baseTransportAntecedent,
  )
  backward.record(
    'discharge inline-base first-sum goal',
    deiterationStep(
      backward.diagram,
      baseTransportConsequent,
      baseTransportFirstGoal,
    ),
  )
  backward.record(
    'discharge inline-base outer goal',
    deiterationStep(
      backward.diagram,
      baseTransportConsequent,
      baseTransportOuterGoal,
    ),
  )

  void baseZero
  void baseAtRight
  void baseAtInner
  void transportedInner
  return {
    name: 'associativityCarrierBase',
    lhs,
    rhs,
    actions: forward.actions,
    backActions: backward.actions,
  }
}
