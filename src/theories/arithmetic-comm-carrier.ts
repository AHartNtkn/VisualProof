import { IOTA, relSig } from '../kernel/diagram/sig'
import type { NodeId, Region, RegionId, WireId } from '../kernel/diagram/diagram'
import { findDeiterationEvidence } from '../kernel/rules/iteration'
import type { ProofContext } from '../kernel/proof/context'
import { bareWireAssembly } from '../kernel/rules/identity-rules'
import type { Theorem } from '../kernel/proof/theorem'
import {
  BINARY,
  TERNARY,
  UNARY,
  commutativityCarrierContent,
  directCuts,
  directNodes,
  endpointWire,
  exactOne,
  relationApplicationContent,
  relationWire,
  rightIdentityCarrierContent,
  scopedWires,
  successorShiftCarrierContent,
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
import { PrimitiveStepRecorder, onlyNewCut, onlyNewNode, onlyNewWire } from './record'
import type { ArithmeticStatements } from './statements'

function deiterateNode(
  recorder: PrimitiveStepRecorder,
  label: string,
  region: RegionId,
  node: NodeId,
): void {
  const sel = { region, regions: [], nodes: [node], wires: [] } as const
  const evidence = findDeiterationEvidence(recorder.diagram, sel)
  recorder.record(label, {
    rule: 'deiteration',
    sel,
    justifier: evidence.justifier,
    certificate: evidence.certificate,
  })
}

function zeroUniqueContent() {
  let graph = emptyGraph()
  const zero = declareWire(graph, graph.root, UNARY)
  graph = zero.graph
  const variables = quantifierScope(
    graph,
    graph.root,
    'forall',
    [IOTA, IOTA],
  )
  const [first, second] = variables.value.variables
  const claim = implication(variables.graph, variables.value.body)
  graph = atom(
    claim.graph,
    claim.value.antecedent,
    zero.value,
    [first!],
  ).graph
  graph = atom(
    graph,
    claim.value.antecedent,
    zero.value,
    [second!],
  ).graph
  graph = identity(
    graph,
    claim.value.consequent,
    [first!, second!],
  ).graph
  return finishDiagramWithBoundary(graph, [zero.value])
}

type LocalCitation = {
  readonly facts: readonly RegionId[]
}

function exposeClosedCitation(
  recorder: PrimitiveStepRecorder,
  name:
    | 'plusLeftUnit'
    | 'plusRightUnit'
    | 'succShiftS'
    | 'successorShiftCarrierInductive'
    | 'rightIdentityCarrierInductive',
  target: RegionId,
  reviewedZero: WireId,
  reviewedSuccessor: WireId,
  reviewedPlus: WireId,
): LocalCitation {
  let before = recorder.diagram
  recorder.record(`cite ${name} locally`, {
    rule: 'theorem',
    name,
    direction: 'forward',
    at: {
      sel: { region: target, regions: [], nodes: [], wires: [] },
      args: [],
    },
  })
  const citedScope = onlyNewCut(before, recorder.diagram, target)
  const citedBody = exactOne(
    directCuts(recorder.diagram, citedScope),
    `${name} cited primitive body`,
  )
  const citedHypotheses = exactOne(
    directCuts(recorder.diagram, citedBody),
    `${name} cited hypotheses`,
  )
  const citedConclusion = exactOne(
    directCuts(recorder.diagram, citedHypotheses).filter((region) =>
      scopedWires(recorder.diagram, region).length === 0),
    `${name} cited conclusion`,
  )
  const citedFacts = directCuts(recorder.diagram, citedConclusion)
  if (citedFacts.length === 0) {
    throw new Error(`${name} cited conclusion contains no facts`)
  }
  const isInside = (region: RegionId, ancestor: RegionId): boolean => {
    let cursor: RegionId | null = region
    while (cursor !== null) {
      if (cursor === ancestor) return true
      const current: Region | undefined = recorder.diagram.regions[cursor]
      cursor = current?.kind === 'cut' ? current.parent : null
    }
    return false
  }
  const citedNats: {
    readonly region: RegionId
    readonly individual: WireId
    readonly scope: RegionId
  }[] = []
  for (const [nodeId, node] of Object.entries(recorder.diagram.nodes)) {
    if (
      isInside(node.region, citedConclusion)
      && node.kind === 'ref'
      && node.defId === 'nat'
    ) {
      const individual = endpointWire(recorder.diagram, nodeId, 'arg', 2)
      const prior = recorder.diagram
      recorder.record(`unfold ${name} cited Nat`, {
        rule: 'unfold',
        nodeId,
      })
      citedNats.push({
        region: node.region,
        individual,
        scope: onlyNewCut(prior, recorder.diagram, node.region),
      })
    }
  }
  for (const [outer, inner, signature] of [
    [reviewedZero, relationWire(recorder.diagram, citedScope, UNARY), UNARY],
    [reviewedPlus, relationWire(recorder.diagram, citedScope, TERNARY), TERNARY],
  ] as const) {
    recorder.recordRelationJoin(`specialize ${name} primitive`, {
    wire: inner,
        content: relationApplicationContent(signature),
        parameters: [outer],
  })
  }
  if (name !== 'plusLeftUnit') {
    recorder.recordRelationJoin(`specialize ${name} successor primitive`, {
    wire: relationWire(recorder.diagram, citedScope, BINARY),
        content: relationApplicationContent(BINARY),
        parameters: [reviewedSuccessor],
  })
  }
  for (const citedNat of citedNats) {
    recorder.record(`refold ${name} cited Nat`, {
      rule: 'fold',
      occurrence: {
        region: citedNat.region,
        regions: [citedNat.scope],
        nodes: [],
        wires: [],
      },
      args: [
        reviewedZero,
        reviewedSuccessor,
        citedNat.individual,
      ],
      defId: 'nat',
    })
  }
  for (const citedHypothesis of directCuts(recorder.diagram, citedHypotheses)
    .filter((region) => region !== citedConclusion)) {
    const sel = {
      region: citedHypotheses,
      regions: [citedHypothesis],
      nodes: [],
      wires: [],
    } as const
    const evidence = findDeiterationEvidence(recorder.diagram, sel)
    recorder.record(`discharge ${name} standing hypothesis`, {
      rule: 'deiteration',
      sel,
      justifier: evidence.justifier,
      certificate: evidence.certificate,
      })
  }
  recorder.record(`expose ${name} conclusion`, {
    rule: 'doubleCutElim',
    region: citedHypotheses,
  })
  recorder.record(`remove ${name} primitive scope`, {
    rule: 'doubleCutElim',
    region: citedScope,
  })
  return { facts: citedFacts }
}

export function commutativityCarrierInductive(
  statements: ArithmeticStatements,
  context: ProofContext,
): Theorem {
  const lhs = finishDiagramWithBoundary(emptyGraph(), [])
  const forward = new PrimitiveStepRecorder(lhs, context)
  forward.record('seed exact commutativity shell from successor shift', {
    rule: 'theorem',
    name: 'succShiftS',
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
  const forwardPrimitiveScope = exactOne(directCuts(forward.diagram, forward.diagram.root), 'support forward primitive scope')
  const forwardPrimitiveBody = exactOne(directCuts(forward.diagram, forwardPrimitiveScope), 'support forward primitive body')
  const forwardHypotheses = exactOne(directCuts(forward.diagram, forwardPrimitiveBody), 'support forward hypotheses')
  const forwardConclusion = exactOne(
    directCuts(forward.diagram, forwardHypotheses).filter((region) =>
      scopedWires(forward.diagram, region).length === 0),
    'support forward conclusion',
  )
  const forwardShift = exactOne(
    directCuts(forward.diagram, forwardConclusion),
    'support forward successor-shift fact',
  )
  const forwardZero = relationWire(forward.diagram, forwardPrimitiveScope, UNARY)
  const forwardSuccessor = relationWire(forward.diagram, forwardPrimitiveScope, BINARY)
  const forwardPlus = relationWire(forward.diagram, forwardPrimitiveScope, TERNARY)
  let before = forward.diagram
  forward.record('introduce zeroUnique hypothesis handle', {
    rule: 'vacuity',
    direction: 'insert',
    assembly: bareWireAssembly('zeroUnique', forwardHypotheses, relSig([])),
  })
  const forwardZeroUnique = onlyNewWire(
    before,
    forward.diagram,
    forwardHypotheses,
  )
  forward.record('assert zeroUnique hypothesis handle', {
    rule: 'atomSpawn',
    region: forwardHypotheses,
    wire: forwardZeroUnique,
  })
  forward.recordRelationJoin('ground exact zeroUnique hypothesis', {
    wire: forwardZeroUnique,
      content: zeroUniqueContent(),
      parameters: [forwardZero],
  })
  const forwardLeftUnit = exposeClosedCitation(
    forward,
    'plusLeftUnit',
    forwardConclusion,
    forwardZero,
    forwardSuccessor,
    forwardPlus,
  ).facts[0]!
  const forwardRightUnit = exposeClosedCitation(
    forward,
    'plusRightUnit',
    forwardConclusion,
    forwardZero,
    forwardSuccessor,
    forwardPlus,
  ).facts[0]!
  const forwardShiftCarrier = exposeClosedCitation(
    forward,
    'successorShiftCarrierInductive',
    forwardConclusion,
    forwardZero,
    forwardSuccessor,
    forwardPlus,
  ).facts
  if (forwardShiftCarrier.length !== 2) {
    throw new Error('expected successor-shift support base and closure')
  }
  const forwardRightCarrier = exposeClosedCitation(
    forward,
    'rightIdentityCarrierInductive',
    forwardConclusion,
    forwardZero,
    forwardSuccessor,
    forwardPlus,
  ).facts
  if (forwardRightCarrier.length !== 2) {
    throw new Error('expected right-identity support base and closure')
  }
  before = forward.diagram
  forward.record('open commutativity-support fixed-right scope', {
    rule: 'doubleCutIntro',
    sel: { region: forwardConclusion, regions: [], nodes: [], wires: [] },
  })
  const forwardSupportScope = onlyNewCut(before, forward.diagram, forwardConclusion)
  const forwardSupportBody = exactOne(directCuts(forward.diagram, forwardSupportScope), 'support forward body')
  forward.record('introduce support fixed right', {
    rule: 'vacuity',
    direction: 'insert',
    assembly: bareWireAssembly('supportFixedRight', forwardSupportScope, IOTA),
  })
  const forwardFixedRight = exactOne(scopedWires(forward.diagram, forwardSupportScope), 'support forward fixed right')
  before = forward.diagram
  forward.record('open commutativity-support implication', {
    rule: 'doubleCutIntro',
    sel: { region: forwardSupportBody, regions: [], nodes: [], wires: [] },
  })
  const forwardSupportAntecedent = onlyNewCut(before, forward.diagram, forwardSupportBody)
  const forwardSupportConsequent = exactOne(directCuts(forward.diagram, forwardSupportAntecedent), 'support forward consequent')
  for (const [label, fact] of [
    ['left-unit', forwardLeftUnit],
    ['right-unit', forwardRightUnit],
    ['successor-shift', forwardShift],
    ['successor-shift base', forwardShiftCarrier[0]!],
    ['successor-shift closure', forwardShiftCarrier[1]!],
    ['right-identity base', forwardRightCarrier[0]!],
    ['right-identity closure', forwardRightCarrier[1]!],
  ] as const) {
    forward.record(`copy ${label} fact into support`, {
      rule: 'iteration',
      sel: {
        region: forwardConclusion,
        regions: [fact],
        nodes: [],
        wires: [],
      },
      target: forwardSupportAntecedent,
      })
  }
  forward.record('erase positive support fact sources', {
    rule: 'erasure',
    sel: {
      region: forwardConclusion,
      regions: [
        forwardLeftUnit,
        forwardRightUnit,
        forwardShift,
        ...forwardShiftCarrier,
        ...forwardRightCarrier,
      ],
      nodes: [],
      wires: [],
    },
  })
  const introduceForward = (
    scope: RegionId,
    labels: readonly string[],
  ): WireId[] => labels.map((label) => {
    const prior = forward.diagram
    forward.record(`introduce ${label}`, {
      rule: 'vacuity',
      direction: 'insert',
      assembly: bareWireAssembly('individual', scope, IOTA),
    })
    return onlyNewWire(prior, forward.diagram, scope)
  })
  const spawnForward = (
    label: string,
    region: RegionId,
    relation: WireId,
    args: readonly WireId[],
  ): NodeId => {
    const prior = forward.diagram
    forward.record(`spawn ${label}`, {
      rule: 'atomSpawn',
      region,
      wire: relation,
    })
    const node = onlyNewNode(prior, forward.diagram, region)
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
  const insertForwardIdentity = (
    label: string,
    region: RegionId,
    wires: readonly WireId[],
  ): NodeId => {
    const prior = forward.diagram
    forward.record(`insert ${label}`, {
      rule: 'identityInsert',
      region,
      wires,
    })
    return onlyNewNode(prior, forward.diagram, region)
  }
  const materializeForwardCarrier = (
    label: string,
    region: RegionId,
    individual: WireId,
    content: ReturnType<typeof successorShiftCarrierContent>,
    parameters: readonly WireId[],
  ): void => {
    let prior = forward.diagram
    forward.record(`introduce ${label} temporary carrier`, {
      rule: 'vacuity',
      direction: 'insert',
      assembly: bareWireAssembly('temporaryCarrier', region, UNARY),
    })
    const temporary = onlyNewWire(prior, forward.diagram, region)
    prior = forward.diagram
    forward.record(`apply ${label} temporary carrier`, {
      rule: 'atomSpawn',
      region,
      wire: temporary,
    })
    const application = onlyNewNode(prior, forward.diagram, region)
    forward.record(`attach ${label} carrier individual`, {
      rule: 'wireJoin',
      input: {
        a: individual,
        b: endpointWire(forward.diagram, application, 'arg', 0),
      },
    })
    forward.recordRelationJoin(`ground ${label} carrier`, {
    wire: temporary,
        content,
        parameters,
  })
  }

  materializeForwardCarrier(
    'fixed-right successor-shift',
    forwardSupportAntecedent,
    forwardFixedRight,
    successorShiftCarrierContent(),
    [forwardSuccessor, forwardPlus],
  )
  materializeForwardCarrier(
    'fixed-right right-identity',
    forwardSupportAntecedent,
    forwardFixedRight,
    rightIdentityCarrierContent(),
    [forwardZero, forwardPlus],
  )

  before = forward.diagram
  forward.record('open forward commutativity carrier base', {
    rule: 'doubleCutIntro',
    sel: {
      region: forwardSupportConsequent,
      regions: [],
      nodes: [],
      wires: [],
    },
  })
  const forwardBase = onlyNewCut(
    before,
    forward.diagram,
    forwardSupportConsequent,
  )
  const forwardBaseBody = exactOne(
    directCuts(forward.diagram, forwardBase),
    'forward commutativity base body',
  )
  const [forwardBaseValue] = introduceForward(
    forwardBase,
    ['forward commutativity base value'],
  )
  before = forward.diagram
  forward.record('open forward commutativity base implication', {
    rule: 'doubleCutIntro',
    sel: {
      region: forwardBaseBody,
      regions: [],
      nodes: [],
      wires: [],
    },
  })
  const forwardBaseAntecedent = onlyNewCut(
    before,
    forward.diagram,
    forwardBaseBody,
  )
  const forwardBaseConsequent = exactOne(
    directCuts(forward.diagram, forwardBaseAntecedent),
    'forward commutativity base consequent',
  )
  spawnForward(
    'forward commutativity base Zero',
    forwardBaseAntecedent,
    forwardZero,
    [forwardBaseValue!],
  )

  before = forward.diagram
  forward.record('open forward commutativity base totality', {
    rule: 'doubleCutIntro',
    sel: {
      region: forwardBaseConsequent,
      regions: [],
      nodes: [],
      wires: [],
    },
  })
  const forwardBaseTotality = onlyNewCut(
    before,
    forward.diagram,
    forwardBaseConsequent,
  )
  const [forwardBaseRight] = introduceForward(
    forwardBaseTotality,
    ['forward commutativity base totality right'],
  )
  spawnForward(
    'forward commutativity base totality Plus',
    forwardBaseTotality,
    forwardPlus,
    [forwardBaseValue!, forwardBaseRight!, forwardBaseRight!],
  )

  before = forward.diagram
  forward.record('open forward commutativity base crossed scope', {
    rule: 'doubleCutIntro',
    sel: {
      region: forwardBaseConsequent,
      regions: [],
      nodes: [],
      wires: [],
    },
  })
  const forwardBaseCross = onlyNewCut(
    before,
    forward.diagram,
    forwardBaseConsequent,
  )
  const forwardBaseCrossBody = exactOne(
    directCuts(forward.diagram, forwardBaseCross),
    'forward commutativity base crossed body',
  )
  const [forwardBaseOutput] = introduceForward(
    forwardBaseCross,
    ['forward commutativity base output'],
  )
  before = forward.diagram
  forward.record('open forward commutativity base crossed implication', {
    rule: 'doubleCutIntro',
    sel: {
      region: forwardBaseCrossBody,
      regions: [],
      nodes: [],
      wires: [],
    },
  })
  const forwardBaseCrossAntecedent = onlyNewCut(
    before,
    forward.diagram,
    forwardBaseCrossBody,
  )
  spawnForward(
    'forward commutativity base premise',
    forwardBaseCrossAntecedent,
    forwardPlus,
    [forwardBaseValue!, forwardFixedRight, forwardBaseOutput!],
  )
  // The inherited output is not a separate existential: a third identity
  // port to a co-scoped wire would carry no semantics (one-point rule), so
  // the inherited totality lands directly on the fixed right.
  insertForwardIdentity(
    'forward commutativity base unit identities',
    forwardBaseCrossAntecedent,
    [
      forwardFixedRight,
      forwardBaseOutput!,
    ],
  )
  spawnForward(
    'forward commutativity base inherited totality',
    forwardBaseCrossAntecedent,
    forwardPlus,
    [
      forwardFixedRight,
      forwardBaseValue!,
      forwardBaseOutput!,
    ],
  )
  spawnForward(
    'forward commutativity base right-identity result',
    forwardBaseCrossAntecedent,
    forwardPlus,
    [forwardFixedRight, forwardBaseValue!, forwardFixedRight],
  )

  before = forward.diagram
  forward.record('open forward commutativity carrier closure', {
    rule: 'doubleCutIntro',
    sel: {
      region: forwardSupportConsequent,
      regions: [],
      nodes: [],
      wires: [],
    },
  })
  const forwardClosure = onlyNewCut(
    before,
    forward.diagram,
    forwardSupportConsequent,
  )
  const forwardClosureBody = exactOne(
    directCuts(forward.diagram, forwardClosure),
    'forward commutativity closure body',
  )
  const [forwardPredecessor, forwardSuccessorValue] = introduceForward(
    forwardClosure,
    [
      'forward commutativity predecessor',
      'forward commutativity successor',
    ],
  )
  before = forward.diagram
  forward.record('open forward commutativity closure implication', {
    rule: 'doubleCutIntro',
    sel: {
      region: forwardClosureBody,
      regions: [],
      nodes: [],
      wires: [],
    },
  })
  const forwardClosureAntecedent = onlyNewCut(
    before,
    forward.diagram,
    forwardClosureBody,
  )
  const forwardClosureConsequent = exactOne(
    directCuts(forward.diagram, forwardClosureAntecedent),
    'forward commutativity closure consequent',
  )
  spawnForward(
    'forward commutativity closure successor premise',
    forwardClosureAntecedent,
    forwardSuccessor,
    [forwardPredecessor!, forwardSuccessorValue!],
  )
  materializeForwardCarrier(
    'inherited commutativity',
    forwardClosureAntecedent,
    forwardPredecessor!,
    commutativityCarrierContent(),
    [forwardPlus, forwardFixedRight],
  )

  before = forward.diagram
  forward.record('open forward commutativity closure totality', {
    rule: 'doubleCutIntro',
    sel: {
      region: forwardClosureConsequent,
      regions: [],
      nodes: [],
      wires: [],
    },
  })
  const forwardClosureTotality = onlyNewCut(
    before,
    forward.diagram,
    forwardClosureConsequent,
  )
  const [
    forwardClosureRight,
    forwardClosureOutput,
    forwardClosureOutputSuccessor,
  ] = introduceForward(
    forwardClosureTotality,
    [
      'forward closure totality right',
      'forward closure totality output',
      'forward closure totality output successor',
    ],
  )
  spawnForward(
    'forward inherited closure-totality Plus',
    forwardClosureTotality,
    forwardPlus,
    [
      forwardPredecessor!,
      forwardClosureRight!,
      forwardClosureOutput!,
    ],
  )
  spawnForward(
    'forward closure-totality output successor',
    forwardClosureTotality,
    forwardSuccessor,
    [forwardClosureOutput!, forwardClosureOutputSuccessor!],
  )
  spawnForward(
    'forward closure-totality stepped Plus',
    forwardClosureTotality,
    forwardPlus,
    [
      forwardSuccessorValue!,
      forwardClosureRight!,
      forwardClosureOutputSuccessor!,
    ],
  )

  before = forward.diagram
  forward.record('open forward commutativity closure crossed scope', {
    rule: 'doubleCutIntro',
    sel: {
      region: forwardClosureConsequent,
      regions: [],
      nodes: [],
      wires: [],
    },
  })
  const forwardClosureCross = onlyNewCut(
    before,
    forward.diagram,
    forwardClosureConsequent,
  )
  const forwardClosureCrossBody = exactOne(
    directCuts(forward.diagram, forwardClosureCross),
    'forward closure crossed body',
  )
  const [forwardCrossOutput] = introduceForward(
    forwardClosureCross,
    ['forward closure crossed output'],
  )
  before = forward.diagram
  forward.record('open forward closure crossed implication', {
    rule: 'doubleCutIntro',
    sel: {
      region: forwardClosureCrossBody,
      regions: [],
      nodes: [],
      wires: [],
    },
  })
  const forwardClosureCrossAntecedent = onlyNewCut(
    before,
    forward.diagram,
    forwardClosureCrossBody,
  )
  const [
    forwardPredecessorOutput,
    forwardPredecessorOutputSuccessor,
    forwardPublicShiftPredecessor,
  ] = introduceForward(
    forwardClosureCrossAntecedent,
    [
      'forward crossed predecessor output',
      'forward crossed predecessor output successor',
      'forward cited-shift predecessor',
    ],
  )
  spawnForward(
    'forward closure crossed premise',
    forwardClosureCrossAntecedent,
    forwardPlus,
    [forwardSuccessorValue!, forwardFixedRight, forwardCrossOutput!],
  )
  spawnForward(
    'forward predecessor fixed-right Plus',
    forwardClosureCrossAntecedent,
    forwardPlus,
    [
      forwardPredecessor!,
      forwardFixedRight,
      forwardPredecessorOutput!,
    ],
  )
  spawnForward(
    'forward predecessor-output successor',
    forwardClosureCrossAntecedent,
    forwardSuccessor,
    [forwardPredecessorOutput!, forwardPredecessorOutputSuccessor!],
  )
  spawnForward(
    'forward stepped fixed-right Plus',
    forwardClosureCrossAntecedent,
    forwardPlus,
    [
      forwardSuccessorValue!,
      forwardFixedRight,
      forwardPredecessorOutputSuccessor!,
    ],
  )
  spawnForward(
    'forward inherited crossed Plus',
    forwardClosureCrossAntecedent,
    forwardPlus,
    [
      forwardFixedRight,
      forwardPredecessor!,
      forwardPredecessorOutput!,
    ],
  )
  spawnForward(
    'forward shifted crossed Plus',
    forwardClosureCrossAntecedent,
    forwardPlus,
    [
      forwardFixedRight,
      forwardSuccessorValue!,
      forwardPredecessorOutputSuccessor!,
    ],
  )
  // id(crossed output, predecessor output successor) has one outer wire
  // (the crossed output), so the one-point collapse merges the successor
  // into it on the spot; everything below uses the survivor.
  forward.record('insert forward crossed output identity', {
    rule: 'identityInsert',
    region: forwardClosureCrossAntecedent,
    wires: [forwardCrossOutput!, forwardPredecessorOutputSuccessor!],
  })
  spawnForward(
    'forward cited-shift predecessor successor',
    forwardClosureCrossAntecedent,
    forwardSuccessor,
    [
      forwardPublicShiftPredecessor!,
      forwardCrossOutput!,
    ],
  )
  spawnForward(
    'forward cited-shift predecessor Plus',
    forwardClosureCrossAntecedent,
    forwardPlus,
    [
      forwardFixedRight,
      forwardPredecessor!,
      forwardPublicShiftPredecessor!,
    ],
  )

  const rhs = statements.commutativityCarrierInductive
  const backward = new PrimitiveStepRecorder(rhs, context, 'backward')
  const primitiveScope = exactOne(directCuts(backward.diagram, backward.diagram.root), 'support reviewed primitive scope')
  const primitiveBody = exactOne(directCuts(backward.diagram, primitiveScope), 'support reviewed primitive body')
  const hypotheses = exactOne(directCuts(backward.diagram, primitiveBody), 'support reviewed hypotheses')
  const conclusion = exactOne(
    directCuts(backward.diagram, hypotheses).filter((region) =>
      scopedWires(backward.diagram, region).length === 0),
    'support reviewed conclusion',
  )
  const supportScope = exactOne(directCuts(backward.diagram, conclusion), 'support reviewed fixed-right scope')
  const supportBody = exactOne(directCuts(backward.diagram, supportScope), 'support reviewed body')
  const supportAntecedent = exactOne(directCuts(backward.diagram, supportBody), 'support reviewed antecedent')
  const supportConsequent = exactOne(directCuts(backward.diagram, supportAntecedent), 'support reviewed consequent')
  const fixedRight = exactOne(scopedWires(backward.diagram, supportScope), 'support reviewed fixed right')
  const reviewedZero = relationWire(backward.diagram, primitiveScope, UNARY)
  const reviewedSuccessor = relationWire(backward.diagram, primitiveScope, BINARY)
  const reviewedPlus = relationWire(backward.diagram, primitiveScope, TERNARY)
  const externalShiftCarrier = exposeClosedCitation(
    backward,
    'successorShiftCarrierInductive',
    supportAntecedent,
    reviewedZero,
    reviewedSuccessor,
    reviewedPlus,
  ).facts
  if (externalShiftCarrier.length !== 2) {
    throw new Error('expected cited successor-shift base and closure')
  }
  const externalRightCarrier = exposeClosedCitation(
    backward,
    'rightIdentityCarrierInductive',
    supportAntecedent,
    reviewedZero,
    reviewedSuccessor,
    reviewedPlus,
  ).facts
  if (externalRightCarrier.length !== 2) {
    throw new Error('expected cited right-identity base and closure')
  }
  const supportNat = exactOne(
    directNodes(backward.diagram, supportAntecedent).filter((node) =>
      backward.diagram.nodes[node]!.kind === 'ref'
      && backward.diagram.nodes[node]!.defId === 'nat'),
    'support fixed-right Nat',
  )
  backward.record('retain support Nat for arithmetic citations', {
    rule: 'iteration',
    sel: {
      region: supportAntecedent,
      regions: [],
      nodes: [supportNat],
      wires: [],
    },
    target: supportAntecedent,
  })
  backward.record('retain support Nat for right-identity carrier', {
    rule: 'iteration',
    sel: {
      region: supportAntecedent,
      regions: [],
      nodes: [supportNat],
      wires: [],
    },
    target: supportAntecedent,
  })
  backward.record('unfold support fixed-right Nat', {
    rule: 'unfold',
    nodeId: supportNat,
  })
  const propertyScope = exactOne(
    directCuts(backward.diagram, supportAntecedent).filter((region) =>
      scopedWires(backward.diagram, region).some((wire) =>
        backward.diagram.wires[wire]!.sig.kind === 'rel')),
    'support Nat property scope',
  )
  const propertyBody = exactOne(
    directCuts(backward.diagram, propertyScope),
    'support Nat property body',
  )
  const property = relationWire(backward.diagram, propertyScope, UNARY)
  backward.recordRelationJoin('ground support Nat to successor-shift carrier', {
    wire: property,
      content: successorShiftCarrierContent(),
      parameters: [reviewedSuccessor, reviewedPlus],
  })
  const hereditary = exactOne(
    directCuts(backward.diagram, propertyBody),
    'support Nat hereditary condition',
  )
  const nestedConditions = directCuts(backward.diagram, hereditary)
  const nestedBase = exactOne(
    nestedConditions.filter((region) =>
      scopedWires(backward.diagram, region).length === 1),
    'support Nat nested base',
  )
  const nestedClosure = exactOne(
    nestedConditions.filter((region) =>
      scopedWires(backward.diagram, region).length === 2),
    'support Nat nested closure',
  )
  for (const [label, region, fact] of [
    ['base', nestedBase, externalShiftCarrier[0]!],
    ['closure', nestedClosure, externalShiftCarrier[1]!],
  ] as const) {
    const sel = {
      region: hereditary,
      regions: [region],
      nodes: [],
      wires: [],
    } as const
    const evidence = findDeiterationEvidence(backward.diagram, sel)
    backward.record(`discharge support Nat ${label}`, {
      rule: 'deiteration',
      sel,
      justifier: evidence.justifier,
      certificate: evidence.certificate,
      })
    void fact
  }
  backward.record('expose support inherited successor-shift carrier', {
    rule: 'doubleCutElim',
    region: hereditary,
  })
  backward.record('remove support grounded Nat property scope', {
    rule: 'doubleCutElim',
    region: propertyScope,
  })
  const rightCarrierNat = exactOne(
    directNodes(backward.diagram, supportAntecedent)
      .filter((node) =>
        backward.diagram.nodes[node]!.kind === 'ref'
        && backward.diagram.nodes[node]!.defId === 'nat')
      .slice(0, 1),
    'right-identity carrier Nat copy',
  )
  backward.record('unfold right-identity carrier Nat copy', {
    rule: 'unfold',
    nodeId: rightCarrierNat,
  })
  const rightPropertyScope = exactOne(
    directCuts(backward.diagram, supportAntecedent).filter((region) =>
      scopedWires(backward.diagram, region).some((wire) =>
        backward.diagram.wires[wire]!.sig.kind === 'rel')),
    'right-identity Nat property scope',
  )
  const rightPropertyBody = exactOne(
    directCuts(backward.diagram, rightPropertyScope),
    'right-identity Nat property body',
  )
  const rightProperty = relationWire(
    backward.diagram,
    rightPropertyScope,
    UNARY,
  )
  backward.recordRelationJoin('ground support Nat to right-identity carrier', {
    wire: rightProperty,
      content: rightIdentityCarrierContent(),
      parameters: [reviewedZero, reviewedPlus],
  })
  const rightHereditary = exactOne(
    directCuts(backward.diagram, rightPropertyBody),
    'right-identity Nat hereditary',
  )
  const rightConditions = directCuts(backward.diagram, rightHereditary)
  const rightNestedBase = exactOne(
    rightConditions.filter((region) =>
      scopedWires(backward.diagram, region).length === 1),
    'right-identity Nat base',
  )
  const rightNestedClosure = exactOne(
    rightConditions.filter((region) =>
      scopedWires(backward.diagram, region).length === 2),
    'right-identity Nat closure',
  )
  const rightConclusion = exactOne(
    rightConditions.filter((region) =>
      scopedWires(backward.diagram, region).length === 0),
    'right-identity Nat conclusion',
  )
  const inheritedRightCarrier = exactOne(
    directCuts(backward.diagram, rightConclusion),
    'inherited right-identity carrier',
  )
  for (const [label, region] of [
    ['base', rightNestedBase],
    ['closure', rightNestedClosure],
  ] as const) {
    const sel = {
      region: rightHereditary,
      regions: [region],
      nodes: [],
      wires: [],
    } as const
    const evidence = findDeiterationEvidence(backward.diagram, sel)
    backward.record(`discharge right-identity Nat ${label}`, {
      rule: 'deiteration',
      sel,
      justifier: evidence.justifier,
      certificate: evidence.certificate,
      })
  }
  backward.record('expose inherited right-identity carrier', {
    rule: 'doubleCutElim',
    region: rightHereditary,
  })
  backward.record('remove grounded right-identity Nat property scope', {
    rule: 'doubleCutElim',
    region: rightPropertyScope,
  })
  const backwardLeftUnit = exposeClosedCitation(
    backward,
    'plusLeftUnit',
    supportAntecedent,
    reviewedZero,
    reviewedSuccessor,
    reviewedPlus,
  ).facts[0]!
  const backwardRightUnit = exposeClosedCitation(
    backward,
    'plusRightUnit',
    supportAntecedent,
    reviewedZero,
    reviewedSuccessor,
    reviewedPlus,
  ).facts[0]!
  const backwardShift = exposeClosedCitation(
    backward,
    'succShiftS',
    supportAntecedent,
    reviewedZero,
    reviewedSuccessor,
    reviewedPlus,
  ).facts[0]!

  const hypothesisChildren = directCuts(backward.diagram, hypotheses)
  const zeroUnique = exactOne(
    hypothesisChildren.filter((region) => {
      if (scopedWires(backward.diagram, region).length !== 2) {
        return false
      }
      const body = exactOne(
        directCuts(backward.diagram, region),
        'binary hypothesis body',
      )
      const antecedent = exactOne(
        directCuts(backward.diagram, body),
        'binary hypothesis antecedent',
      )
      return directNodes(backward.diagram, antecedent).length === 2
    }),
    'zeroUnique hypothesis',
  )
  const additionBase = exactOne(
    hypothesisChildren.filter((region) => {
      if (scopedWires(backward.diagram, region).length !== 2) {
        return false
      }
      const body = exactOne(
        directCuts(backward.diagram, region),
        'binary hypothesis body',
      )
      const antecedent = exactOne(
        directCuts(backward.diagram, body),
        'binary hypothesis antecedent',
      )
      return directNodes(backward.diagram, antecedent).length === 1
    }),
    'plusBase hypothesis',
  )
  const additionFunctional = exactOne(
    hypothesisChildren.filter((region) =>
      scopedWires(backward.diagram, region).length === 4),
    'plusSingleValued hypothesis',
  )
  const supportConditions = directCuts(backward.diagram, supportConsequent)
  const baseCondition = exactOne(
    supportConditions.filter((region) =>
      scopedWires(backward.diagram, region).length === 1),
    'commutativity support base',
  )
  const closureCondition = exactOne(
    supportConditions.filter((region) =>
      scopedWires(backward.diagram, region).length === 2),
    'commutativity support closure',
  )
  const baseConditionBody = exactOne(
    directCuts(backward.diagram, baseCondition),
    'commutativity support base body',
  )
  const baseConditionAntecedent = exactOne(
    directCuts(backward.diagram, baseConditionBody),
    'commutativity support base antecedent',
  )
  const baseConditionConsequent = exactOne(
    directCuts(backward.diagram, baseConditionAntecedent),
    'commutativity support base consequent',
  )
  const baseValue = exactOne(
    scopedWires(backward.diagram, baseCondition),
    'commutativity support base value',
  )
  const baseZero = exactOne(
    directNodes(backward.diagram, baseConditionAntecedent),
    'commutativity support base Zero',
  )
  before = backward.diagram
  backward.record('copy zero uniqueness for commutativity base', {
    rule: 'iteration',
    sel: {
      region: hypotheses,
      regions: [zeroUnique],
      nodes: [],
      wires: [],
    },
    target: baseConditionAntecedent,
  })
  const copiedZeroUnique = onlyNewCut(
    before,
    backward.diagram,
    baseConditionAntecedent,
  )
  const copiedZeroUniqueBody = exactOne(
    directCuts(backward.diagram, copiedZeroUnique),
    'copied zero uniqueness body',
  )
  const copiedZeroUniqueAntecedent = exactOne(
    directCuts(backward.diagram, copiedZeroUniqueBody),
    'copied zero uniqueness antecedent',
  )
  const zeroVariables = scopedWires(backward.diagram, copiedZeroUnique)
  backward.record('specialize first commutativity-base zero', {
    rule: 'wireJoin',
    input: { a: baseValue, b: zeroVariables[0]! },
  })
  backward.record('specialize second commutativity-base zero', {
    rule: 'wireJoin',
    input: { a: baseValue, b: zeroVariables[1]! },
  })
  for (const node of directNodes(backward.diagram, copiedZeroUniqueAntecedent)) {
    deiterateNode(
      backward,
      'discharge commutativity-base zero premise',
      copiedZeroUniqueAntecedent,
      node,
    )
  }
  backward.record('expose commutativity-base zero identity', {
    rule: 'doubleCutElim',
    region: copiedZeroUniqueAntecedent,
  })
  backward.record('finish commutativity-base zero uniqueness', {
    rule: 'doubleCutElim',
    region: copiedZeroUnique,
  })

  const baseCarrierScopes = directCuts(
    backward.diagram,
    baseConditionConsequent,
  )
  const baseTotality = exactOne(
    baseCarrierScopes.filter((region) => {
      const body = directCuts(backward.diagram, region)[0]
      return body !== undefined
        && directNodes(backward.diagram, body).length === 1
    }),
    'commutativity-base totality',
  )
  const baseCommutativity = exactOne(
    baseCarrierScopes.filter((region) => region !== baseTotality),
    'commutativity-base crossed implication',
  )
  const baseTotalityRight = exactOne(
    scopedWires(backward.diagram, baseTotality),
    'commutativity-base totality right',
  )
  const baseTotalityBody = exactOne(
    directCuts(backward.diagram, baseTotality),
    'commutativity-base totality body',
  )
  const baseTotalityGoal = exactOne(
    directNodes(backward.diagram, baseTotalityBody),
    'commutativity-base totality goal',
  )
  const baseTotalityOutput = endpointWire(
    backward.diagram,
    baseTotalityGoal,
    'arg',
    2,
  )
  before = backward.diagram
  backward.record('copy addition base into commutativity-base totality', {
    rule: 'iteration',
    sel: {
      region: hypotheses,
      regions: [additionBase],
      nodes: [],
      wires: [],
    },
    target: baseTotality,
  })
  const copiedAdditionBase = onlyNewCut(before, backward.diagram, baseTotality)
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
    directNodes(backward.diagram, copiedAdditionBaseAntecedent),
    'copied addition-base Zero',
  )
  const copiedAdditionBaseResult = exactOne(
    directNodes(backward.diagram, copiedAdditionBaseConsequent),
    'copied addition-base result',
  )
  backward.record('specialize addition-base zero in commutativity totality', {
    rule: 'wireJoin',
    input: {
      a: baseValue,
      b: endpointWire(backward.diagram, copiedAdditionBaseZero, 'arg', 0),
    },
  })
  backward.record('specialize addition-base right in commutativity totality', {
    rule: 'wireJoin',
    input: {
      a: baseTotalityRight,
      b: endpointWire(backward.diagram, copiedAdditionBaseResult, 'arg', 1),
    },
  })
  deiterateNode(
    backward,
    'discharge copied commutativity-totality Zero',
    copiedAdditionBaseAntecedent,
    copiedAdditionBaseZero,
  )
  backward.record('expose copied commutativity addition-base result', {
    rule: 'doubleCutElim',
    region: copiedAdditionBaseAntecedent,
  })
  backward.record('finish commutativity addition-base specialization', {
    rule: 'doubleCutElim',
    region: copiedAdditionBase,
  })
  backward.record('choose base-totality right as output', {
    rule: 'wireJoin',
    input: {
      a: baseTotalityRight,
      b: baseTotalityOutput,
    },
  })
  {
    const selection = {
      region: baseTotalityBody,
      regions: [],
      nodes: [baseTotalityGoal],
      wires: [],
    } as const
    const evidence = findDeiterationEvidence(backward.diagram, selection)
    backward.record('discharge commutativity-base totality', {
      rule: 'deiteration',
      sel: selection,
      justifier: evidence.justifier,
      certificate: evidence.certificate,
      })
  }
  void copiedAdditionBaseResult
  const baseCommutativityBody = exactOne(
    directCuts(backward.diagram, baseCommutativity),
    'commutativity-base crossed body',
  )
  const baseCommutativityAntecedent = exactOne(
    directCuts(backward.diagram, baseCommutativityBody),
    'commutativity-base crossed antecedent',
  )
  const baseCommutativityConsequent = exactOne(
    directCuts(backward.diagram, baseCommutativityAntecedent),
    'commutativity-base crossed consequent',
  )
  const baseCommutativityPremise = exactOne(
    directNodes(backward.diagram, baseCommutativityAntecedent),
    'commutativity-base Plus premise',
  )
  const baseCommutativityGoal = exactOne(
    directNodes(backward.diagram, baseCommutativityConsequent),
    'commutativity-base crossed Plus goal',
  )
  const baseCommutativityOutput = endpointWire(
    backward.diagram,
    baseCommutativityPremise,
    'arg',
    2,
  )

  before = backward.diagram
  backward.record('retain commutativity-base Zero for unit citation', {
    rule: 'iteration',
    sel: {
      region: baseConditionAntecedent,
      regions: [],
      nodes: [baseZero],
      wires: [],
    },
    target: baseCommutativityAntecedent,
  })
  const retainedBaseZero = onlyNewNode(
    before,
    backward.diagram,
    baseCommutativityAntecedent,
  )
  before = backward.diagram
  backward.record('copy left-unit fact into commutativity base', {
    rule: 'iteration',
    sel: {
      region: supportAntecedent,
      regions: [backwardLeftUnit],
      nodes: [],
      wires: [],
    },
    target: baseCommutativityAntecedent,
  })
  const copiedBaseLeftUnit = onlyNewCut(
    before,
    backward.diagram,
    baseCommutativityAntecedent,
  )
  const copiedBaseLeftUnitBody = exactOne(
    directCuts(backward.diagram, copiedBaseLeftUnit),
    'commutativity-base copied left-unit body',
  )
  const copiedBaseLeftUnitAntecedent = exactOne(
    directCuts(backward.diagram, copiedBaseLeftUnitBody),
    'commutativity-base copied left-unit antecedent',
  )
  const copiedBaseLeftUnitZero = exactOne(
    directNodes(backward.diagram, copiedBaseLeftUnitAntecedent)
      .filter((node) =>
        endpointWire(backward.diagram, node, 'head') === reviewedZero),
    'commutativity-base copied left-unit Zero',
  )
  const copiedBaseLeftUnitPlus = exactOne(
    directNodes(backward.diagram, copiedBaseLeftUnitAntecedent)
      .filter((node) =>
        endpointWire(backward.diagram, node, 'head') === reviewedPlus),
    'commutativity-base copied left-unit Plus',
  )
  for (const [label, outer, inner] of [
    [
      'zero',
      baseValue,
      endpointWire(backward.diagram, copiedBaseLeftUnitZero, 'arg', 0),
    ],
    [
      'addend',
      fixedRight,
      endpointWire(backward.diagram, copiedBaseLeftUnitPlus, 'arg', 1),
    ],
    [
      'output',
      baseCommutativityOutput,
      endpointWire(backward.diagram, copiedBaseLeftUnitPlus, 'arg', 2),
    ],
  ] as const) {
    backward.record(`specialize commutativity-base left-unit ${label}`, {
      rule: 'wireJoin',
      input: { a: outer, b: inner },
    })
  }
  deiterateNode(
    backward,
    'discharge commutativity-base left-unit Zero premise',
    copiedBaseLeftUnitAntecedent,
    exactOne(
      directNodes(backward.diagram, copiedBaseLeftUnitAntecedent)
        .filter((node) =>
          endpointWire(backward.diagram, node, 'head') === reviewedZero),
      'commutativity-base left-unit Zero premise',
    ),
  )
  deiterateNode(
    backward,
    'discharge commutativity-base left-unit Plus premise',
    copiedBaseLeftUnitAntecedent,
    exactOne(
      directNodes(backward.diagram, copiedBaseLeftUnitAntecedent)
        .filter((node) =>
          endpointWire(backward.diagram, node, 'head') === reviewedPlus),
      'commutativity-base left-unit Plus premise',
    ),
  )
  backward.record('expose commutativity-base left-unit identity', {
    rule: 'doubleCutElim',
    region: copiedBaseLeftUnitAntecedent,
  })
  backward.record('finish commutativity-base left-unit specialization', {
    rule: 'doubleCutElim',
    region: copiedBaseLeftUnit,
  })
  deiterateNode(
    backward,
    'remove retained commutativity-base Zero',
    baseCommutativityAntecedent,
    retainedBaseZero,
  )

  const inheritedShiftScopes = directCuts(
    backward.diagram,
    supportAntecedent,
  )
  const inheritedShiftTotality = exactOne(
    inheritedShiftScopes.filter((region) => {
      if (scopedWires(backward.diagram, region).length !== 1) return false
      const body = directCuts(backward.diagram, region)[0]
      return body !== undefined
        && directNodes(backward.diagram, body).some((node) =>
          endpointWire(backward.diagram, node, 'head') === reviewedPlus)
    }),
    'inherited fixed-right totality',
  )
  before = backward.diagram
  backward.record('copy inherited totality into commutativity base', {
    rule: 'iteration',
    sel: {
      region: supportAntecedent,
      regions: [inheritedShiftTotality],
      nodes: [],
      wires: [],
    },
    target: baseCommutativityAntecedent,
  })
  const copiedBaseTotality = onlyNewCut(
    before,
    backward.diagram,
    baseCommutativityAntecedent,
  )
  backward.record('specialize inherited totality at base zero', {
    rule: 'wireJoin',
    input: {
      a: baseValue,
      b: exactOne(
        scopedWires(backward.diagram, copiedBaseTotality),
        'copied inherited-totality input',
      ),
    },
  })
  const copiedBaseTotalityBody = exactOne(
    directCuts(backward.diagram, copiedBaseTotality),
    'copied inherited-totality body',
  )
  const inheritedBasePlus = exactOne(
    directNodes(backward.diagram, copiedBaseTotalityBody),
    'inherited commutativity-base Plus',
  )
  const inheritedBaseOutput = endpointWire(
    backward.diagram,
    inheritedBasePlus,
    'arg',
    2,
  )
  backward.record('expose inherited commutativity-base Plus', {
    rule: 'doubleCutElim',
    region: copiedBaseTotality,
  })

  before = backward.diagram
  backward.record('copy right-unit fact into commutativity base', {
    rule: 'iteration',
    sel: {
      region: supportAntecedent,
      regions: [backwardRightUnit],
      nodes: [],
      wires: [],
    },
    target: baseCommutativityAntecedent,
  })
  const copiedBaseRightUnit = onlyNewCut(
    before,
    backward.diagram,
    baseCommutativityAntecedent,
  )
  const copiedBaseRightUnitBody = exactOne(
    directCuts(backward.diagram, copiedBaseRightUnit),
    'commutativity-base copied right-unit body',
  )
  const copiedBaseRightUnitAntecedent = exactOne(
    directCuts(backward.diagram, copiedBaseRightUnitBody),
    'commutativity-base copied right-unit antecedent',
  )
  const copiedBaseRightUnitConsequent = exactOne(
    directCuts(backward.diagram, copiedBaseRightUnitAntecedent),
    'commutativity-base copied right-unit consequent',
  )
  const copiedBaseRightUnitZero = exactOne(
    directNodes(backward.diagram, copiedBaseRightUnitAntecedent)
      .filter((node) =>
        backward.diagram.nodes[node]!.kind === 'atom'
        && endpointWire(backward.diagram, node, 'head') === reviewedZero),
    'commutativity-base copied right-unit Zero',
  )
  const copiedBaseRightUnitPlus = exactOne(
    directNodes(backward.diagram, copiedBaseRightUnitAntecedent)
      .filter((node) =>
        backward.diagram.nodes[node]!.kind === 'atom'
        && endpointWire(backward.diagram, node, 'head') === reviewedPlus),
    'commutativity-base copied right-unit Plus',
  )
  for (const [label, outer, inner] of [
    [
      'zero',
      baseValue,
      endpointWire(backward.diagram, copiedBaseRightUnitZero, 'arg', 0),
    ],
    [
      'addend',
      fixedRight,
      endpointWire(backward.diagram, copiedBaseRightUnitPlus, 'arg', 0),
    ],
    [
      'output',
      inheritedBaseOutput,
      endpointWire(backward.diagram, copiedBaseRightUnitPlus, 'arg', 2),
    ],
  ] as const) {
    backward.record(`specialize commutativity-base right-unit ${label}`, {
      rule: 'wireJoin',
      input: { a: outer, b: inner },
    })
  }
  for (const node of directNodes(
    backward.diagram,
    copiedBaseRightUnitAntecedent,
  )) {
    const sel = {
      region: copiedBaseRightUnitAntecedent,
      regions: [],
      nodes: [node],
      wires: [],
    } as const
    const evidence = findDeiterationEvidence(backward.diagram, sel)
    backward.record('discharge commutativity-base right-unit premise', {
      rule: 'deiteration',
      sel,
      justifier: evidence.justifier,
      certificate: evidence.certificate,
      })
  }
  const baseRightIdentity = exactOne(
    directNodes(backward.diagram, copiedBaseRightUnitConsequent),
    'commutativity-base right-unit identity',
  )
  backward.record('expose commutativity-base right-unit identity', {
    rule: 'doubleCutElim',
    region: copiedBaseRightUnitAntecedent,
  })
  backward.record('finish commutativity-base right-unit specialization', {
    rule: 'doubleCutElim',
    region: copiedBaseRightUnit,
  })
  before = backward.diagram
  backward.record('copy inherited right-identity carrier into base', {
    rule: 'iteration',
    sel: {
      region: supportAntecedent,
      regions: [inheritedRightCarrier],
      nodes: [],
      wires: [],
    },
    target: baseCommutativityAntecedent,
  })
  const copiedInheritedRightCarrier = onlyNewCut(
    before,
    backward.diagram,
    baseCommutativityAntecedent,
  )
  backward.record('specialize inherited right identity at base zero', {
    rule: 'wireJoin',
    input: {
      a: baseValue,
      b: exactOne(
        scopedWires(backward.diagram, copiedInheritedRightCarrier),
        'copied right-identity zero',
      ),
    },
  })
  const copiedInheritedRightCarrierBody = exactOne(
    directCuts(backward.diagram, copiedInheritedRightCarrier),
    'copied right-identity body',
  )
  const copiedInheritedRightCarrierAntecedent = exactOne(
    directCuts(backward.diagram, copiedInheritedRightCarrierBody),
    'copied right-identity antecedent',
  )
  const copiedInheritedRightCarrierConsequent = exactOne(
    directCuts(backward.diagram, copiedInheritedRightCarrierAntecedent),
    'copied right-identity consequent',
  )
  const copiedInheritedRightZero = exactOne(
    directNodes(backward.diagram, copiedInheritedRightCarrierAntecedent),
    'copied right-identity Zero',
  )
  deiterateNode(
    backward,
    'discharge inherited right-identity Zero',
    copiedInheritedRightCarrierAntecedent,
    copiedInheritedRightZero,
  )
  const inheritedRightPlus = exactOne(
    directNodes(backward.diagram, copiedInheritedRightCarrierConsequent),
    'inherited right-identity Plus',
  )
  backward.record('expose inherited right-identity Plus', {
    rule: 'doubleCutElim',
    region: copiedInheritedRightCarrierAntecedent,
  })
  backward.record('finish inherited right-identity specialization', {
    rule: 'doubleCutElim',
    region: copiedInheritedRightCarrier,
  })
  const baseUnitIdentity = exactOne(
    Object.entries(backward.diagram.nodes)
      .filter(([, node]) => node.kind === 'identity')
      .filter(([identity]) => {
        const incident = Object.entries(backward.diagram.wires)
          .filter(([, wire]) =>
            wire.endpoints.some((endpoint) =>
              endpoint.node === identity))
          .map(([wire]) => wire)
        return incident.includes(fixedRight)
          && incident.includes(baseCommutativityOutput)
      })
      .map(([identity]) => identity),
    'combined commutativity-base unit identity',
  )
  // Substitution is the derivation (no retargets): severing the fixed
  // right so the unit identity keeps one co-scoped end makes the one-point
  // collapse land the inherited result's output endpoint on the base
  // output. This consumes the identity; addition functionality re-derives
  // it below, once the crossed goal has discharged against the result.
  backward.record('land the inherited result on the base output', {
    rule: 'wireSever',
    input: {
      wire: fixedRight,
      keep: backward.diagram.wires[fixedRight]!.endpoints.filter((endpoint) =>
        endpoint.node !== baseUnitIdentity
        && !(
          endpoint.node === inheritedRightPlus
          && endpoint.port.kind === 'arg'
          && endpoint.port.index === 2
        )),
      scope: baseCommutativityAntecedent,
    },
  })
  deiterateNode(
    backward,
    'discharge commutativity-base crossed goal',
    baseCommutativityConsequent,
    baseCommutativityGoal,
  )
  before = backward.diagram
  backward.record('copy addition functionality to restore the unit identity', {
    rule: 'iteration',
    sel: {
      region: hypotheses,
      regions: [additionFunctional],
      nodes: [],
      wires: [],
    },
    target: baseCommutativityAntecedent,
  })
  const restoredFunctional = onlyNewCut(
    before,
    backward.diagram,
    baseCommutativityAntecedent,
  )
  const restoredFunctionalBody = exactOne(
    directCuts(backward.diagram, restoredFunctional),
    'restored functionality body',
  )
  const restoredFunctionalAntecedent = exactOne(
    directCuts(backward.diagram, restoredFunctionalBody),
    'restored functionality antecedent',
  )
  const restoredFunctionalConsequent = exactOne(
    directCuts(backward.diagram, restoredFunctionalAntecedent),
    'restored functionality consequent',
  )
  const restoredFunctionalVariables = scopedWires(
    backward.diagram,
    restoredFunctional,
  )
  for (const [label, outer, inner] of [
    ['left', fixedRight, restoredFunctionalVariables[0]!],
    ['right', baseValue, restoredFunctionalVariables[1]!],
    ['first output', baseCommutativityOutput, restoredFunctionalVariables[2]!],
    ['second output', fixedRight, restoredFunctionalVariables[3]!],
  ] as const) {
    backward.record(`specialize restored functionality ${label}`, {
      rule: 'wireJoin',
      input: { a: outer, b: inner },
    })
  }
  for (const node of directNodes(
    backward.diagram,
    restoredFunctionalAntecedent,
  )) {
    deiterateNode(
      backward,
      'discharge restored functionality premise',
      restoredFunctionalAntecedent,
      node,
    )
  }
  exactOne(
    directNodes(backward.diagram, restoredFunctionalConsequent),
    'restored unit identity',
  )
  backward.record('expose restored unit identity', {
    rule: 'doubleCutElim',
    region: restoredFunctionalAntecedent,
  })
  backward.record('finish restoring the unit identity', {
    rule: 'doubleCutElim',
    region: restoredFunctional,
  })
  void inheritedBasePlus
  void baseRightIdentity
  const successorTotal = exactOne(
    hypothesisChildren.filter((region) =>
      scopedWires(backward.diagram, region).length === 1),
    'successorTotal hypothesis',
  )
  const additionStep = exactOne(
    hypothesisChildren.filter((region) =>
      scopedWires(backward.diagram, region).length === 5),
    'plusStep hypothesis',
  )
  const closureBody = exactOne(
    directCuts(backward.diagram, closureCondition),
    'commutativity closure body',
  )
  const closureAntecedent = exactOne(
    directCuts(backward.diagram, closureBody),
    'commutativity closure antecedent',
  )
  const closureConsequent = exactOne(
    directCuts(backward.diagram, closureAntecedent).filter((region) =>
      scopedWires(backward.diagram, region).length === 0),
    'commutativity closure consequent',
  )
  const [closurePredecessor, closureSuccessorValue] = scopedWires(
    backward.diagram,
    closureCondition,
  )
  if (closurePredecessor === undefined || closureSuccessorValue === undefined) {
    throw new Error('missing commutativity closure variables')
  }
  const closureSuccessorNode = exactOne(
    directNodes(backward.diagram, closureAntecedent).filter((node) =>
      endpointWire(backward.diagram, node, 'head') === reviewedSuccessor),
    'commutativity closure successor premise',
  )
  void closureSuccessorNode
  const inheritedClosureScopes = directCuts(
    backward.diagram,
    closureAntecedent,
  ).filter((region) => region !== closureConsequent)
  const inheritedClosureTotality = exactOne(
    inheritedClosureScopes.filter((region) => {
      const body = directCuts(backward.diagram, region)[0]
      return body !== undefined
        && directNodes(backward.diagram, body).length === 1
    }),
    'inherited commutativity closure totality',
  )
  const inheritedClosureCommutativity = exactOne(
    inheritedClosureScopes.filter((region) =>
      region !== inheritedClosureTotality),
    'inherited commutativity closure crossed implication',
  )
  const closureGoalScopes = directCuts(
    backward.diagram,
    closureConsequent,
  )
  const closureGoalTotality = exactOne(
    closureGoalScopes.filter((region) => {
      const body = directCuts(backward.diagram, region)[0]
      return body !== undefined
        && directNodes(backward.diagram, body).length === 1
    }),
    'commutativity closure goal totality',
  )
  const closureGoalCommutativity = exactOne(
    closureGoalScopes.filter((region) =>
      region !== closureGoalTotality),
    'commutativity closure crossed goal',
  )
  before = backward.diagram
  backward.record('copy inherited totality into closure totality', {
    rule: 'iteration',
    sel: {
      region: closureAntecedent,
      regions: [inheritedClosureTotality],
      nodes: [],
      wires: [],
    },
    target: closureGoalTotality,
  })
  const copiedClosureInheritedTotality = onlyNewCut(
    before,
    backward.diagram,
    closureGoalTotality,
  )
  const closureGoalRight = exactOne(
    scopedWires(backward.diagram, closureGoalTotality),
    'commutativity closure totality right',
  )
  backward.record('specialize inherited closure totality right', {
    rule: 'wireJoin',
    input: {
      a: closureGoalRight,
      b: exactOne(
        scopedWires(backward.diagram, copiedClosureInheritedTotality),
        'copied inherited closure-totality input',
      ),
    },
  })
  const copiedClosureInheritedTotalityBody = exactOne(
    directCuts(backward.diagram, copiedClosureInheritedTotality),
    'copied inherited closure-totality body',
  )
  const inheritedClosurePlus = exactOne(
    directNodes(backward.diagram, copiedClosureInheritedTotalityBody),
    'copied inherited closure-totality Plus',
  )
  const inheritedClosureOutput = endpointWire(
    backward.diagram,
    inheritedClosurePlus,
    'arg',
    2,
  )
  backward.record('expose inherited closure-totality Plus', {
    rule: 'doubleCutElim',
    region: copiedClosureInheritedTotality,
  })

  before = backward.diagram
  backward.record('copy successor totality into closure totality', {
    rule: 'iteration',
    sel: {
      region: hypotheses,
      regions: [successorTotal],
      nodes: [],
      wires: [],
    },
    target: closureGoalTotality,
  })
  const copiedClosureSuccessorTotal = onlyNewCut(
    before,
    backward.diagram,
    closureGoalTotality,
  )
  const copiedClosureSuccessorTotalBody = exactOne(
    directCuts(backward.diagram, copiedClosureSuccessorTotal),
    'copied closure successor-totality body',
  )
  const closureOutputSuccessorNode = exactOne(
    directNodes(backward.diagram, copiedClosureSuccessorTotalBody),
    'copied closure output successor',
  )
  backward.record('specialize closure output successor input', {
    rule: 'wireJoin',
    input: {
      a: inheritedClosureOutput,
      b: endpointWire(
        backward.diagram,
        closureOutputSuccessorNode,
        'arg',
        0,
      ),
    },
  })
  const closureOutputSuccessor = endpointWire(
    backward.diagram,
    closureOutputSuccessorNode,
    'arg',
    1,
  )
  backward.record('expose closure output successor', {
    rule: 'doubleCutElim',
    region: copiedClosureSuccessorTotal,
  })

  before = backward.diagram
  backward.record('copy addition step into closure totality', {
    rule: 'iteration',
    sel: {
      region: hypotheses,
      regions: [additionStep],
      nodes: [],
      wires: [],
    },
    target: closureGoalTotality,
  })
  const copiedClosureStep = onlyNewCut(
    before,
    backward.diagram,
    closureGoalTotality,
  )
  const copiedClosureStepBody = exactOne(
    directCuts(backward.diagram, copiedClosureStep),
    'copied closure step body',
  )
  const copiedClosureStepAntecedent = exactOne(
    directCuts(backward.diagram, copiedClosureStepBody),
    'copied closure step antecedent',
  )
  const copiedClosureStepConsequent = exactOne(
    directCuts(backward.diagram, copiedClosureStepAntecedent),
    'copied closure step consequent',
  )
  const copiedClosureStepPremises = directNodes(
    backward.diagram,
    copiedClosureStepAntecedent,
  )
  const copiedClosureStepPlus = exactOne(
    copiedClosureStepPremises.filter((node) =>
      endpointWire(backward.diagram, node, 'head') === reviewedPlus),
    'copied closure step Plus',
  )
  const copiedClosureStepSuccessors = copiedClosureStepPremises.filter((node) =>
    endpointWire(backward.diagram, node, 'head') === reviewedSuccessor)
  const copiedClosureStepResult = exactOne(
    directNodes(backward.diagram, copiedClosureStepConsequent),
    'copied closure step result',
  )
  const copiedClosureLeftSuccessor = exactOne(
    copiedClosureStepSuccessors.filter((node) =>
      endpointWire(backward.diagram, node, 'arg', 0)
      === endpointWire(backward.diagram, copiedClosureStepPlus, 'arg', 0)),
    'copied closure left successor',
  )
  const copiedClosureOutputSuccessor = exactOne(
    copiedClosureStepSuccessors.filter((node) =>
      endpointWire(backward.diagram, node, 'arg', 0)
      === endpointWire(backward.diagram, copiedClosureStepPlus, 'arg', 2)),
    'copied closure output successor',
  )
  for (const [label, outer, inner] of [
    ['predecessor', closurePredecessor, endpointWire(backward.diagram, copiedClosureStepPlus, 'arg', 0)],
    ['right', closureGoalRight, endpointWire(backward.diagram, copiedClosureStepPlus, 'arg', 1)],
    ['output', inheritedClosureOutput, endpointWire(backward.diagram, copiedClosureStepPlus, 'arg', 2)],
    ['successor', closureSuccessorValue, endpointWire(backward.diagram, copiedClosureLeftSuccessor, 'arg', 1)],
    ['output successor', closureOutputSuccessor, endpointWire(backward.diagram, copiedClosureOutputSuccessor, 'arg', 1)],
  ] as const) {
    backward.record(`specialize closure step ${label}`, {
      rule: 'wireJoin',
      input: { a: outer, b: inner },
    })
  }
  for (const node of directNodes(
    backward.diagram,
    copiedClosureStepAntecedent,
  )) {
    deiterateNode(
      backward,
      'discharge closure step premise',
      copiedClosureStepAntecedent,
      node,
    )
  }
  backward.record('expose closure step result', {
    rule: 'doubleCutElim',
    region: copiedClosureStepAntecedent,
  })
  backward.record('finish closure step specialization', {
    rule: 'doubleCutElim',
    region: copiedClosureStep,
  })
  const closureGoalTotalityBody = exactOne(
    directCuts(backward.diagram, closureGoalTotality)
      .filter((region) =>
        directNodes(backward.diagram, region).length === 1),
    'closure goal totality body',
  )
  const closureGoalTotalityNode = exactOne(
    directNodes(backward.diagram, closureGoalTotalityBody),
    'closure goal totality Plus',
  )
  backward.record('choose closure totality successor output', {
    rule: 'wireJoin',
    input: {
      a: closureOutputSuccessor,
      b: endpointWire(
        backward.diagram,
        closureGoalTotalityNode,
        'arg',
        2,
      ),
    },
  })
  deiterateNode(
    backward,
    'discharge commutativity closure totality goal',
    closureGoalTotalityBody,
    closureGoalTotalityNode,
  )
  void copiedClosureStepResult

  const closureCrossBody = exactOne(
    directCuts(backward.diagram, closureGoalCommutativity),
    'closure crossed body',
  )
  const closureCrossAntecedent = exactOne(
    directCuts(backward.diagram, closureCrossBody),
    'closure crossed antecedent',
  )
  const closureCrossConsequent = exactOne(
    directCuts(backward.diagram, closureCrossAntecedent),
    'closure crossed consequent',
  )
  const closureCrossPremise = exactOne(
    directNodes(backward.diagram, closureCrossAntecedent),
    'closure crossed premise',
  )
  const closureCrossGoal = exactOne(
    directNodes(backward.diagram, closureCrossConsequent),
    'closure crossed goal',
  )
  const closureCrossOutput = endpointWire(
    backward.diagram,
    closureCrossPremise,
    'arg',
    2,
  )

  before = backward.diagram
  backward.record('copy predecessor totality into closure crossed proof', {
    rule: 'iteration',
    sel: {
      region: closureAntecedent,
      regions: [inheritedClosureTotality],
      nodes: [],
      wires: [],
    },
    target: closureCrossAntecedent,
  })
  const copiedCrossPredecessorTotality = onlyNewCut(
    before,
    backward.diagram,
    closureCrossAntecedent,
  )
  backward.record('specialize predecessor totality at fixed right', {
    rule: 'wireJoin',
    input: {
      a: fixedRight,
      b: exactOne(
        scopedWires(backward.diagram, copiedCrossPredecessorTotality),
        'crossed predecessor-totality input',
      ),
    },
  })
  const copiedCrossPredecessorTotalityBody = exactOne(
    directCuts(backward.diagram, copiedCrossPredecessorTotality),
    'crossed predecessor-totality body',
  )
  const predecessorPlus = exactOne(
    directNodes(backward.diagram, copiedCrossPredecessorTotalityBody),
    'crossed predecessor Plus',
  )
  const predecessorOutput = endpointWire(
    backward.diagram,
    predecessorPlus,
    'arg',
    2,
  )
  backward.record('expose crossed predecessor Plus', {
    rule: 'doubleCutElim',
    region: copiedCrossPredecessorTotality,
  })

  before = backward.diagram
  backward.record('copy successor totality into closure crossed proof', {
    rule: 'iteration',
    sel: {
      region: hypotheses,
      regions: [successorTotal],
      nodes: [],
      wires: [],
    },
    target: closureCrossAntecedent,
  })
  const copiedCrossSuccessorTotality = onlyNewCut(
    before,
    backward.diagram,
    closureCrossAntecedent,
  )
  const copiedCrossSuccessorTotalityBody = exactOne(
    directCuts(backward.diagram, copiedCrossSuccessorTotality),
    'crossed successor-totality body',
  )
  const predecessorOutputSuccessorNode = exactOne(
    directNodes(backward.diagram, copiedCrossSuccessorTotalityBody),
    'crossed predecessor-output successor',
  )
  backward.record('specialize predecessor-output successor', {
    rule: 'wireJoin',
    input: {
      a: predecessorOutput,
      b: endpointWire(
        backward.diagram,
        predecessorOutputSuccessorNode,
        'arg',
        0,
      ),
    },
  })
  const predecessorOutputSuccessor = endpointWire(
    backward.diagram,
    predecessorOutputSuccessorNode,
    'arg',
    1,
  )
  backward.record('expose predecessor-output successor', {
    rule: 'doubleCutElim',
    region: copiedCrossSuccessorTotality,
  })

  before = backward.diagram
  backward.record('copy addition step into closure crossed proof', {
    rule: 'iteration',
    sel: {
      region: hypotheses,
      regions: [additionStep],
      nodes: [],
      wires: [],
    },
    target: closureCrossAntecedent,
  })
  const copiedCrossStep = onlyNewCut(
    before,
    backward.diagram,
    closureCrossAntecedent,
  )
  const copiedCrossStepBody = exactOne(
    directCuts(backward.diagram, copiedCrossStep),
    'crossed addition-step body',
  )
  const copiedCrossStepAntecedent = exactOne(
    directCuts(backward.diagram, copiedCrossStepBody),
    'crossed addition-step antecedent',
  )
  const copiedCrossStepConsequent = exactOne(
    directCuts(backward.diagram, copiedCrossStepAntecedent),
    'crossed addition-step consequent',
  )
  const crossStepPremises = directNodes(
    backward.diagram,
    copiedCrossStepAntecedent,
  )
  const crossStepPlus = exactOne(
    crossStepPremises.filter((node) =>
      endpointWire(backward.diagram, node, 'head') === reviewedPlus),
    'crossed step Plus',
  )
  const crossStepSuccessors = crossStepPremises.filter((node) =>
    endpointWire(backward.diagram, node, 'head') === reviewedSuccessor)
  const crossStepLeftSuccessor = exactOne(
    crossStepSuccessors.filter((node) =>
      endpointWire(backward.diagram, node, 'arg', 0)
      === endpointWire(backward.diagram, crossStepPlus, 'arg', 0)),
    'crossed step left successor',
  )
  const crossStepOutputSuccessor = exactOne(
    crossStepSuccessors.filter((node) =>
      endpointWire(backward.diagram, node, 'arg', 0)
      === endpointWire(backward.diagram, crossStepPlus, 'arg', 2)),
    'crossed step output successor',
  )
  for (const [label, outer, inner] of [
    ['predecessor', closurePredecessor, endpointWire(backward.diagram, crossStepPlus, 'arg', 0)],
    ['fixed right', fixedRight, endpointWire(backward.diagram, crossStepPlus, 'arg', 1)],
    ['predecessor output', predecessorOutput, endpointWire(backward.diagram, crossStepPlus, 'arg', 2)],
    ['successor', closureSuccessorValue, endpointWire(backward.diagram, crossStepLeftSuccessor, 'arg', 1)],
    ['output successor', predecessorOutputSuccessor, endpointWire(backward.diagram, crossStepOutputSuccessor, 'arg', 1)],
  ] as const) {
    backward.record(`specialize crossed addition-step ${label}`, {
      rule: 'wireJoin',
      input: { a: outer, b: inner },
    })
  }
  for (const node of directNodes(
    backward.diagram,
    copiedCrossStepAntecedent,
  )) {
    deiterateNode(
      backward,
      'discharge crossed addition-step premise',
      copiedCrossStepAntecedent,
      node,
    )
  }
  const steppedCrossPlus = exactOne(
    directNodes(backward.diagram, copiedCrossStepConsequent),
    'crossed stepped Plus',
  )
  backward.record('expose crossed stepped Plus', {
    rule: 'doubleCutElim',
    region: copiedCrossStepAntecedent,
  })
  backward.record('finish crossed addition-step specialization', {
    rule: 'doubleCutElim',
    region: copiedCrossStep,
  })

  before = backward.diagram
  backward.record('copy inherited commutativity into crossed proof', {
    rule: 'iteration',
    sel: {
      region: closureAntecedent,
      regions: [inheritedClosureCommutativity],
      nodes: [],
      wires: [],
    },
    target: closureCrossAntecedent,
  })
  const copiedInheritedCommutativity = onlyNewCut(
    before,
    backward.diagram,
    closureCrossAntecedent,
  )
  const copiedInheritedCommutativityBody = exactOne(
    directCuts(backward.diagram, copiedInheritedCommutativity),
    'copied inherited commutativity body',
  )
  const copiedInheritedCommutativityAntecedent = exactOne(
    directCuts(backward.diagram, copiedInheritedCommutativityBody),
    'copied inherited commutativity antecedent',
  )
  const copiedInheritedCommutativityConsequent = exactOne(
    directCuts(backward.diagram, copiedInheritedCommutativityAntecedent),
    'copied inherited commutativity consequent',
  )
  backward.record('specialize inherited commutativity output', {
    rule: 'wireJoin',
    input: {
      a: predecessorOutput,
      b: exactOne(
        scopedWires(backward.diagram, copiedInheritedCommutativity),
        'copied inherited commutativity output',
      ),
    },
  })
  const inheritedCommPremise = exactOne(
    directNodes(backward.diagram, copiedInheritedCommutativityAntecedent),
    'copied inherited commutativity premise',
  )
  deiterateNode(
    backward,
    'discharge inherited commutativity premise',
    copiedInheritedCommutativityAntecedent,
    inheritedCommPremise,
  )
  const inheritedCrossedPlus = exactOne(
    directNodes(backward.diagram, copiedInheritedCommutativityConsequent),
    'inherited crossed Plus',
  )
  backward.record('expose inherited crossed Plus', {
    rule: 'doubleCutElim',
    region: copiedInheritedCommutativityAntecedent,
  })
  backward.record('finish inherited commutativity specialization', {
    rule: 'doubleCutElim',
    region: copiedInheritedCommutativity,
  })

  const inheritedShiftTransport = exactOne(
    directCuts(backward.diagram, supportAntecedent).filter((region) =>
      scopedWires(backward.diagram, region).length === 4
      && !Object.values(backward.diagram.nodes).some((node) => {
        if (node.kind !== 'ref') return false
        let cursor: RegionId | null = node.region
        while (cursor !== null) {
          if (cursor === region) return true
          const current: Region | undefined = backward.diagram.regions[cursor]
          cursor = current?.kind === 'cut' ? current.parent : null
        }
        return false
      })),
    'inherited fixed-right successor transport',
  )
  before = backward.diagram
  backward.record('copy fixed-right successor transport into crossed proof', {
    rule: 'iteration',
    sel: {
      region: supportAntecedent,
      regions: [inheritedShiftTransport],
      nodes: [],
      wires: [],
    },
    target: closureCrossAntecedent,
  })
  const copiedShiftTransport = onlyNewCut(
    before,
    backward.diagram,
    closureCrossAntecedent,
  )
  const copiedShiftTransportBody = exactOne(
    directCuts(backward.diagram, copiedShiftTransport),
    'copied shift transport body',
  )
  const copiedShiftTransportAntecedent = exactOne(
    directCuts(backward.diagram, copiedShiftTransportBody),
    'copied shift transport antecedent',
  )
  const copiedShiftTransportConsequent = exactOne(
    directCuts(backward.diagram, copiedShiftTransportAntecedent),
    'copied shift transport consequent',
  )
  const copiedShiftTransportPremises = directNodes(
    backward.diagram,
    copiedShiftTransportAntecedent,
  )
  const copiedShiftTransportPlus = exactOne(
    copiedShiftTransportPremises.filter((node) =>
      endpointWire(backward.diagram, node, 'head') === reviewedPlus),
    'copied shift transport Plus',
  )
  const copiedShiftTransportSuccessors =
    copiedShiftTransportPremises.filter((node) =>
      endpointWire(backward.diagram, node, 'head') === reviewedSuccessor)
  const copiedShiftRight = endpointWire(
    backward.diagram,
    copiedShiftTransportPlus,
    'arg',
    1,
  )
  const copiedShiftOutput = endpointWire(
    backward.diagram,
    copiedShiftTransportPlus,
    'arg',
    2,
  )
  const copiedShiftRightSuccessor = exactOne(
    copiedShiftTransportSuccessors.filter((node) =>
      endpointWire(backward.diagram, node, 'arg', 0) === copiedShiftRight),
    'copied shift right successor',
  )
  const copiedShiftOutputSuccessor = exactOne(
    copiedShiftTransportSuccessors.filter((node) =>
      endpointWire(backward.diagram, node, 'arg', 0) === copiedShiftOutput),
    'copied shift output successor',
  )
  for (const [label, outer, inner] of [
    ['right', closurePredecessor, copiedShiftRight],
    ['right successor', closureSuccessorValue, endpointWire(backward.diagram, copiedShiftRightSuccessor, 'arg', 1)],
    ['output', predecessorOutput, copiedShiftOutput],
    ['output successor', predecessorOutputSuccessor, endpointWire(backward.diagram, copiedShiftOutputSuccessor, 'arg', 1)],
  ] as const) {
    backward.record(`specialize fixed-right transport ${label}`, {
      rule: 'wireJoin',
      input: { a: outer, b: inner },
    })
  }
  for (const node of directNodes(
    backward.diagram,
    copiedShiftTransportAntecedent,
  )) {
    deiterateNode(
      backward,
      'discharge fixed-right transport premise',
      copiedShiftTransportAntecedent,
      node,
    )
  }
  const shiftedCrossedPlus = exactOne(
    directNodes(backward.diagram, copiedShiftTransportConsequent),
    'shifted crossed Plus',
  )
  backward.record('expose fixed-right shifted Plus', {
    rule: 'doubleCutElim',
    region: copiedShiftTransportAntecedent,
  })
  backward.record('finish fixed-right transport specialization', {
    rule: 'doubleCutElim',
    region: copiedShiftTransport,
  })

  before = backward.diagram
  backward.record('copy addition functionality into crossed proof', {
    rule: 'iteration',
    sel: {
      region: hypotheses,
      regions: [additionFunctional],
      nodes: [],
      wires: [],
    },
    target: closureCrossAntecedent,
  })
  const copiedCrossFunctional = onlyNewCut(
    before,
    backward.diagram,
    closureCrossAntecedent,
  )
  const copiedCrossFunctionalBody = exactOne(
    directCuts(backward.diagram, copiedCrossFunctional),
    'crossed addition-functionality body',
  )
  const copiedCrossFunctionalAntecedent = exactOne(
    directCuts(backward.diagram, copiedCrossFunctionalBody),
    'crossed addition-functionality antecedent',
  )
  const copiedCrossFunctionalConsequent = exactOne(
    directCuts(backward.diagram, copiedCrossFunctionalAntecedent),
    'crossed addition-functionality consequent',
  )
  const crossFunctionalVariables = scopedWires(
    backward.diagram,
    copiedCrossFunctional,
  )
  for (const [label, outer, inner] of [
    ['left', closureSuccessorValue, crossFunctionalVariables[0]!],
    ['right', fixedRight, crossFunctionalVariables[1]!],
    ['given output', closureCrossOutput, crossFunctionalVariables[2]!],
    ['stepped output', predecessorOutputSuccessor, crossFunctionalVariables[3]!],
  ] as const) {
    backward.record(`specialize crossed functionality ${label}`, {
      rule: 'wireJoin',
      input: { a: outer, b: inner },
    })
  }
  for (const node of directNodes(
    backward.diagram,
    copiedCrossFunctionalAntecedent,
  )) {
    deiterateNode(
      backward,
      'discharge crossed functionality premise',
      copiedCrossFunctionalAntecedent,
      node,
    )
  }
  exactOne(
    directNodes(backward.diagram, copiedCrossFunctionalConsequent),
    'crossed output identity',
  )
  backward.record('expose crossed output identity', {
    rule: 'doubleCutElim',
    region: copiedCrossFunctionalAntecedent,
  })
  // Finishing exposes id(given output, stepped output) with one outer wire;
  // the one-point collapse merges them on the spot, so the crossed goal
  // discharges directly below.
  backward.record('finish crossed functionality specialization', {
    rule: 'doubleCutElim',
    region: copiedCrossFunctional,
  })

  before = backward.diagram
  backward.record('copy cited successor shift into crossed proof', {
    rule: 'iteration',
    sel: {
      region: supportAntecedent,
      regions: [backwardShift],
      nodes: [],
      wires: [],
    },
    target: closureCrossAntecedent,
  })
  const copiedPublicShift = onlyNewCut(
    before,
    backward.diagram,
    closureCrossAntecedent,
  )
  const copiedPublicShiftBody = exactOne(
    directCuts(backward.diagram, copiedPublicShift),
    'copied public-shift body',
  )
  const copiedPublicShiftAntecedent = exactOne(
    directCuts(backward.diagram, copiedPublicShiftBody),
    'copied public-shift antecedent',
  )
  const copiedPublicShiftConsequent = exactOne(
    directCuts(backward.diagram, copiedPublicShiftAntecedent),
    'copied public-shift consequent',
  )
  const copiedPublicShiftVariables = scopedWires(
    backward.diagram,
    copiedPublicShift,
  )
  for (const [label, outer, inner] of [
    ['left', fixedRight, copiedPublicShiftVariables[0]!],
    ['right', closurePredecessor, copiedPublicShiftVariables[1]!],
    ['right successor', closureSuccessorValue, copiedPublicShiftVariables[2]!],
    ['output', predecessorOutputSuccessor, copiedPublicShiftVariables[3]!],
  ] as const) {
    backward.record(`specialize cited successor shift ${label}`, {
      rule: 'wireJoin',
      input: { a: outer, b: inner },
    })
  }
  for (const node of directNodes(
    backward.diagram,
    copiedPublicShiftAntecedent,
  )) {
    deiterateNode(
      backward,
      'discharge cited successor-shift premise',
      copiedPublicShiftAntecedent,
      node,
    )
  }
  const publicShiftResults = directNodes(
    backward.diagram,
    copiedPublicShiftConsequent,
  )
  if (publicShiftResults.length !== 2) {
    throw new Error('expected cited successor-shift predecessor evidence')
  }
  backward.record('expose cited successor-shift evidence', {
    rule: 'doubleCutElim',
    region: copiedPublicShiftAntecedent,
  })
  backward.record('finish cited successor-shift specialization', {
    rule: 'doubleCutElim',
    region: copiedPublicShift,
  })

  deiterateNode(
    backward,
    'discharge closure crossed goal',
    closureCrossConsequent,
    closureCrossGoal,
  )
  void steppedCrossPlus
  void inheritedCrossedPlus
  void shiftedCrossedPlus
  void publicShiftResults

  const retainedNat = exactOne(
    directNodes(backward.diagram, supportAntecedent).filter((node) =>
      backward.diagram.nodes[node]!.kind === 'ref'
      && backward.diagram.nodes[node]!.defId === 'nat'),
    'retained support Nat',
  )
  backward.record('unfold retained support Nat after citation use', {
    rule: 'unfold',
    nodeId: retainedNat,
  })
  const retainedPropertyScope = exactOne(
    directCuts(backward.diagram, supportAntecedent).filter((region) =>
      scopedWires(backward.diagram, region).some((wire) =>
        backward.diagram.wires[wire]!.sig.kind === 'rel')),
    'retained Nat property scope',
  )
  const retainedPropertyBody = exactOne(
    directCuts(backward.diagram, retainedPropertyScope),
    'retained Nat property body',
  )
  const retainedProperty = relationWire(
    backward.diagram,
    retainedPropertyScope,
    UNARY,
  )
  backward.recordRelationJoin('ground retained Nat to right-identity carrier', {
    wire: retainedProperty,
      content: rightIdentityCarrierContent(),
      parameters: [reviewedZero, reviewedPlus],
  })
  const retainedHereditary = exactOne(
    directCuts(backward.diagram, retainedPropertyBody),
    'retained Nat hereditary',
  )
  const retainedConclusion = exactOne(
    directCuts(backward.diagram, retainedHereditary).filter((region) =>
      scopedWires(backward.diagram, region).length === 0),
    'retained right-identity carrier conclusion',
  )
  const duplicateCarrierScopes = directCuts(
    backward.diagram,
    retainedConclusion,
  )
  const retainedConditions = directCuts(
    backward.diagram,
    retainedHereditary,
  ).filter((region) => region !== retainedConclusion)
  const retainedBase = exactOne(
    retainedConditions.filter((region) =>
      scopedWires(backward.diagram, region).length === 1),
    'retained right-identity base',
  )
  const retainedClosure = exactOne(
    retainedConditions.filter((region) =>
      scopedWires(backward.diagram, region).length === 2),
    'retained right-identity closure',
  )
  for (const [label, region] of [
    ['base', retainedBase],
    ['closure', retainedClosure],
  ] as const) {
    const sel = {
      region: retainedHereditary,
      regions: [region],
      nodes: [],
      wires: [],
    } as const
    const evidence = findDeiterationEvidence(backward.diagram, sel)
    backward.record(`discharge retained right-identity ${label}`, {
      rule: 'deiteration',
      sel,
      justifier: evidence.justifier,
      certificate: evidence.certificate,
      })
  }
  backward.record('expose duplicate right-identity carrier', {
    rule: 'doubleCutElim',
    region: retainedHereditary,
  })
  backward.record('remove retained right-identity property scope', {
    rule: 'doubleCutElim',
    region: retainedPropertyScope,
  })
  for (const region of duplicateCarrierScopes) {
    const sel = {
      region: supportAntecedent,
      regions: [region],
      nodes: [],
      wires: [],
    } as const
    const evidence = findDeiterationEvidence(backward.diagram, sel)
    backward.record('remove duplicate right-identity carrier fact', {
      rule: 'deiteration',
      sel,
      justifier: evidence.justifier,
      certificate: evidence.certificate,
      })
  }
  void baseZero
  void baseCommutativity
  void backwardRightUnit
  void backwardShift
  void additionFunctional
  void closureCondition
  return {
    name: 'commutativityCarrierInductive',
    lhs,
    rhs,
    actions: forward.actions,
    backActions: backward.actions,
  }
}
