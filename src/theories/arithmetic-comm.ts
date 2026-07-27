import { IOTA } from '../kernel/diagram/sig'
import type {
  NodeId,
  Region,
  RegionId,
  WireId,
} from '../kernel/diagram/diagram'
import {
  registerTheorem,
  verifyTheory,
  type ProofContext,
  type Theory,
} from '../kernel/proof/context'
import type { Theorem } from '../kernel/proof/theorem'
import { findDeiterationEvidence } from '../kernel/rules/iteration'
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
  commutativityCarrierInductive,
} from './arithmetic-comm-carrier'
import type { ArithmeticStatements } from './statements'


function deiterateNode(
  recorder: PrimitiveStepRecorder,
  label: string,
  region: RegionId,
  node: NodeId,
): void {
  const sel = { region, regions: [], nodes: [node], wires: [] } as const
  const evidence = findDeiterationEvidence(recorder.diagram, sel, 4096)
  recorder.record(label, {
    rule: 'deiteration',
    sel,
    justifier: evidence.justifier,
    certificate: evidence.certificate,
    retargets: [],
  })
}

function plusComm(
  statements: ArithmeticStatements,
  context: ProofContext,
): Theorem {
  const lhs = finishDiagramWithBoundary(emptyGraph(), [])
  const forward = new PrimitiveStepRecorder(lhs.diagram, context)
  forward.record('seed commutativity shell from carrier support', {
    rule: 'theorem',
    name: 'commutativityCarrierInductive',
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
    'forward hypotheses',
  )
  const forwardConclusion = exactOne(
    directCuts(forward.diagram, forwardHypotheses).filter((region) =>
      scopedWires(forward.diagram, region).length === 0),
    'forward conclusion',
  )
  const forwardClaimScope = exactOne(
    directCuts(forward.diagram, forwardConclusion),
    'forward fixed-right support scope',
  )
  const forwardClaimBody = exactOne(
    directCuts(forward.diagram, forwardClaimScope),
    'forward fixed-right support body',
  )
  const forwardOuterAntecedent = exactOne(
    directCuts(forward.diagram, forwardClaimBody),
    'forward Nat(b) antecedent',
  )
  const forwardOuterConsequent = exactOne(
    directCuts(forward.diagram, forwardOuterAntecedent),
    'forward carrier-support consequent',
  )
  const forwardRight = exactOne(
    scopedWires(forward.diagram, forwardClaimScope),
    'forward fixed right',
  )
  let before = forward.diagram
  forward.record('introduce public left', {
    rule: 'vacuousIntro',
    scope: forwardClaimScope,
    sig: IOTA,
  })
  const forwardLeft = onlyNewWire(
    before,
    forward.diagram,
    forwardClaimScope,
  )
  before = forward.diagram
  forward.record('introduce public output', {
    rule: 'vacuousIntro',
    scope: forwardClaimScope,
    sig: IOTA,
  })
  const forwardOutput = onlyNewWire(
    before,
    forward.diagram,
    forwardClaimScope,
  )
  before = forward.diagram
  forward.record('open nested commutativity implication', {
    rule: 'doubleCutIntro',
    sel: {
      region: forwardOuterConsequent,
      regions: [],
      nodes: [],
      wires: [],
    },
  })
  const forwardInnerAntecedent = onlyNewCut(
    before,
    forward.diagram,
    forwardOuterConsequent,
  )
  const forwardInnerConsequent = exactOne(
    directCuts(forward.diagram, forwardInnerAntecedent),
    'forward nested consequent',
  )
  const forwardSupport = directCuts(
    forward.diagram,
    forwardOuterConsequent,
  ).filter((region) => region !== forwardInnerAntecedent)
  if (forwardSupport.length !== 2) {
    throw new Error(`expected forward Base/Closure, found ${forwardSupport.length}`)
  }
  for (const [index, region] of forwardSupport.entries()) {
    forward.record(`copy carrier support ${index}`, {
      rule: 'iteration',
      sel: {
        region: forwardOuterConsequent,
        regions: [region],
        nodes: [],
        wires: [],
      },
      target: forwardInnerAntecedent,
      retargets: [],
    })
  }
  forward.record('erase positive carrier support', {
    rule: 'erasure',
    sel: {
      region: forwardOuterConsequent,
      regions: forwardSupport,
      nodes: [],
      wires: [],
    },
  })
  forward.record('unfold retained outer Nat(b)', {
    rule: 'unfold',
    nodeId: exactOne(
      directNodes(forward.diagram, forwardOuterAntecedent).filter((node) =>
        forward.diagram.nodes[node]!.kind === 'ref'
        && forward.diagram.nodes[node]!.defId === 'nat'),
      'forward outer Nat(b)',
    ),
  })
  const forwardPlus = relationWire(
    forward.diagram,
    forwardPrimitiveScope,
    TERNARY,
  )
  const spawnForwardPlus = (
    label: string,
    region: RegionId,
    args: readonly WireId[],
  ): NodeId => {
    const prior = forward.diagram
    forward.record(`spawn ${label}`, {
      rule: 'atomSpawn',
      region,
      wire: forwardPlus,
    })
    const node = onlyNewNode(prior, forward.diagram, region)
    args.forEach((wire, index) => {
      forward.record(`attach ${label} ${index}`, {
        rule: 'wireJoin',
        input: {
          kind: 'iota',
          a: wire,
          b: endpointWire(forward.diagram, node, 'arg', index),
        },
      })
    })
    return node
  }
  spawnForwardPlus(
    'public Plus(a,b,o)',
    forwardInnerAntecedent,
    [forwardLeft, forwardRight, forwardOutput],
  )
  const forwardCrossed = spawnForwardPlus(
    'derived Plus(b,a,o)',
    forwardInnerAntecedent,
    [forwardRight, forwardLeft, forwardOutput],
  )
  forward.record('copy derived crossed Plus to goal', {
    rule: 'iteration',
    sel: {
      region: forwardInnerAntecedent,
      regions: [],
      nodes: [forwardCrossed],
      wires: [],
    },
    target: forwardInnerConsequent,
    retargets: [],
  })
  before = forward.diagram
  forward.record('open residual commutativity totality', {
    rule: 'doubleCutIntro',
    sel: {
      region: forwardInnerAntecedent,
      regions: [],
      nodes: [],
      wires: [],
    },
  })
  const forwardTotality = onlyNewCut(
    before,
    forward.diagram,
    forwardInnerAntecedent,
  )
  const forwardTotalityBody = exactOne(
    directCuts(forward.diagram, forwardTotality),
    'forward residual totality body',
  )
  before = forward.diagram
  forward.record('introduce residual totality input', {
    rule: 'vacuousIntro',
    scope: forwardTotality,
    sig: IOTA,
  })
  const forwardTotalityInput = onlyNewWire(
    before,
    forward.diagram,
    forwardTotality,
  )
  before = forward.diagram
  forward.record('introduce residual totality output', {
    rule: 'vacuousIntro',
    scope: forwardTotalityBody,
    sig: IOTA,
  })
  const forwardTotalityOutput = onlyNewWire(
    before,
    forward.diagram,
    forwardTotalityBody,
  )
  spawnForwardPlus(
    'residual commutativity totality',
    forwardTotalityBody,
    [forwardLeft, forwardTotalityInput, forwardTotalityOutput],
  )

  const rhs = statements.plusComm
  const backward = new PrimitiveStepRecorder(
    rhs.diagram,
    context,
    'backward',
  )
  const backwardPrimitiveScope = exactOne(
    directCuts(backward.diagram, backward.diagram.root),
    'backward primitive scope',
  )
  const backwardPrimitiveBody = exactOne(
    directCuts(backward.diagram, backwardPrimitiveScope),
    'backward primitive body',
  )
  const backwardHypotheses = exactOne(
    directCuts(backward.diagram, backwardPrimitiveBody),
    'backward hypotheses',
  )
  const backwardConclusion = exactOne(
    directCuts(backward.diagram, backwardHypotheses).filter((region) =>
      scopedWires(backward.diagram, region).length === 0),
    'backward conclusion',
  )
  const backwardClaimScope = exactOne(
    directCuts(backward.diagram, backwardConclusion),
    'backward public claim scope',
  )
  const backwardClaimBody = exactOne(
    directCuts(backward.diagram, backwardClaimScope),
    'backward public claim body',
  )
  const backwardOuterAntecedent = exactOne(
    directCuts(backward.diagram, backwardClaimBody),
    'backward flat antecedent',
  )
  const backwardOldConsequent = exactOne(
    directCuts(backward.diagram, backwardOuterAntecedent),
    'backward old consequent',
  )
  const [backwardLeft, backwardRight, backwardOutput] =
    scopedWires(backward.diagram, backwardClaimScope)
  if (
    backwardLeft === undefined
    || backwardRight === undefined
    || backwardOutput === undefined
  ) throw new Error('missing backward public variables')
  const backwardPlus = relationWire(
    backward.diagram,
    backwardPrimitiveScope,
    TERNARY,
  )
  const backwardZero = relationWire(
    backward.diagram,
    backwardPrimitiveScope,
    UNARY,
  )
  const backwardSuccessor = relationWire(
    backward.diagram,
    backwardPrimitiveScope,
    BINARY,
  )
  const publicNats = directNodes(
    backward.diagram,
    backwardOuterAntecedent,
  ).filter((node) =>
    backward.diagram.nodes[node]!.kind === 'ref'
    && backward.diagram.nodes[node]!.defId === 'nat')
  const publicLeftNat = exactOne(
    publicNats.filter((node) =>
      endpointWire(backward.diagram, node, 'arg', 2) === backwardLeft),
    'public Nat(a)',
  )
  const publicRightNat = exactOne(
    publicNats.filter((node) =>
      endpointWire(backward.diagram, node, 'arg', 2) === backwardRight),
    'public Nat(b)',
  )
  const publicPlus = exactOne(
    directNodes(backward.diagram, backwardOuterAntecedent).filter((node) =>
      backward.diagram.nodes[node]!.kind === 'atom'
      && endpointWire(backward.diagram, node, 'head') === backwardPlus),
    'public Plus(a,b,o)',
  )
  before = backward.diagram
  backward.record('curry public Nat(b) premise', {
    rule: 'doubleCutIntro',
    sel: {
      region: backwardOuterAntecedent,
      regions: [backwardOldConsequent],
      nodes: [publicLeftNat, publicPlus],
      wires: [],
    },
  })
  const backwardOuterConsequent = onlyNewCut(
    before,
    backward.diagram,
    backwardOuterAntecedent,
  )
  const backwardInnerAntecedent = exactOne(
    directCuts(backward.diagram, backwardOuterConsequent),
    'backward inner antecedent',
  )
  const backwardInnerConsequent = exactOne(
    directCuts(backward.diagram, backwardInnerAntecedent),
    'backward inner consequent',
  )

  before = backward.diagram
  backward.record('cite commutativity carrier support locally', {
    rule: 'theorem',
    name: 'commutativityCarrierInductive',
    direction: 'forward',
    at: {
      sel: {
        region: backwardInnerAntecedent,
        regions: [],
        nodes: [],
        wires: [],
      },
      args: [],
    },
  })
  const citedPrimitiveScope = onlyNewCut(
    before,
    backward.diagram,
    backwardInnerAntecedent,
  )
  const citedPrimitiveBody = exactOne(
    directCuts(backward.diagram, citedPrimitiveScope),
    'cited primitive body',
  )
  const citedHypotheses = exactOne(
    directCuts(backward.diagram, citedPrimitiveBody),
    'cited hypotheses',
  )
  const citedConclusion = exactOne(
    directCuts(backward.diagram, citedHypotheses).filter((region) =>
      scopedWires(backward.diagram, region).length === 0),
    'cited conclusion',
  )
  const citedSupportScope = exactOne(
    directCuts(backward.diagram, citedConclusion),
    'cited quantified support',
  )
  const isInside = (region: RegionId, ancestor: RegionId): boolean => {
    let cursor: RegionId | null = region
    while (cursor !== null) {
      if (cursor === ancestor) return true
      const region: Region | undefined =
        backward.diagram.regions[cursor]
      cursor = region?.kind === 'cut' ? region.parent : null
    }
    return false
  }
  const citedNatNode = exactOne(
    Object.entries(backward.diagram.nodes)
      .filter(([, node]) =>
        isInside(node.region, citedSupportScope)
        && node.kind === 'ref'
        && node.defId === 'nat')
      .map(([id]) => id),
    'cited support Nat(b)',
  )
  const citedNatRegion = backward.diagram.nodes[citedNatNode]!.region
  before = backward.diagram
  backward.record('unfold cited support Nat(b)', {
    rule: 'unfold',
    nodeId: citedNatNode,
  })
  const citedNatScope = onlyNewCut(
    before,
    backward.diagram,
    citedNatRegion,
  )
  for (const [outer, inner, signature] of [
    [
      backwardZero,
      relationWire(backward.diagram, citedPrimitiveScope, UNARY),
      UNARY,
    ],
    [
      backwardSuccessor,
      relationWire(backward.diagram, citedPrimitiveScope, BINARY),
      BINARY,
    ],
    [
      backwardPlus,
      relationWire(backward.diagram, citedPrimitiveScope, TERNARY),
      TERNARY,
    ],
  ] as const) {
    backward.record('specialize cited primitive', {
      rule: 'wireJoin',
      input: {
        kind: 'relation',
        wire: inner,
        content: relationApplicationContent(signature),
        parameters: [outer],
      },
    })
  }
  const outerStandingZero = exactOne(
    directNodes(backward.diagram, backwardHypotheses).filter((node) =>
      endpointWire(backward.diagram, node, 'head') === backwardZero),
    'outer standing Zero',
  )
  const citedStandingZero = exactOne(
    directNodes(backward.diagram, citedHypotheses).filter((node) =>
      endpointWire(backward.diagram, node, 'head') === backwardZero),
    'cited standing Zero',
  )
  backward.record('specialize cited standing Zero', {
    rule: 'wireJoin',
    input: {
      kind: 'iota',
      a: endpointWire(backward.diagram, outerStandingZero, 'arg', 0),
      b: endpointWire(backward.diagram, citedStandingZero, 'arg', 0),
    },
  })
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
    backward.record('discharge cited standing hypothesis', {
      rule: 'deiteration',
      sel,
      justifier: evidence.justifier,
      certificate: evidence.certificate,
      retargets: [],
    })
  }
  deiterateNode(
    backward,
    'discharge cited standing Zero',
    citedHypotheses,
    citedStandingZero,
  )
  backward.record('expose cited support conclusion', {
    rule: 'doubleCutElim',
    region: citedHypotheses,
  })
  backward.record('remove cited primitive scope', {
    rule: 'doubleCutElim',
    region: citedPrimitiveScope,
  })
  const citedFixedRight = exactOne(
    scopedWires(backward.diagram, citedSupportScope),
    'cited fixed right',
  )
  backward.record('specialize cited support at outer right', {
    rule: 'wireJoin',
    input: {
      kind: 'iota',
      a: backwardRight,
      b: citedFixedRight,
    },
  })
  const citedSupportBody = exactOne(
    directCuts(backward.diagram, citedSupportScope),
    'cited support body',
  )
  const citedSupportAntecedent = exactOne(
    directCuts(backward.diagram, citedSupportBody),
    'cited support antecedent',
  )
  backward.record('remove cited support quantifier shell', {
    rule: 'doubleCutElim',
    region: citedSupportScope,
  })
  before = backward.diagram
  backward.record('unfold public Nat(b)', {
    rule: 'unfold',
    nodeId: publicRightNat,
  })
  onlyNewCut(
    before,
    backward.diagram,
    backwardOuterAntecedent,
  )
  {
    const sel = {
      region: citedSupportAntecedent,
      regions: [citedNatScope],
      nodes: [],
      wires: [],
    } as const
    const evidence = findDeiterationEvidence(
      backward.diagram,
      sel,
      4096,
    )
    backward.record('discharge unfolded cited Nat(b)', {
      rule: 'deiteration',
      sel,
      justifier: evidence.justifier,
      certificate: evidence.certificate,
      retargets: [],
    })
  }
  backward.record('expose local Base and Closure', {
    rule: 'doubleCutElim',
    region: citedSupportAntecedent,
  })
  const externalBase = exactOne(
    directCuts(backward.diagram, backwardInnerAntecedent).filter((region) =>
      region !== backwardInnerConsequent
      && scopedWires(backward.diagram, region).length === 1),
    'external commutativity base',
  )
  const externalClosure = exactOne(
    directCuts(backward.diagram, backwardInnerAntecedent).filter((region) =>
      region !== backwardInnerConsequent
      && scopedWires(backward.diagram, region).length === 2),
    'external commutativity closure',
  )

  before = backward.diagram
  backward.record('unfold public Nat(a)', {
    rule: 'unfold',
    nodeId: publicLeftNat,
  })
  const propertyScope = onlyNewCut(
    before,
    backward.diagram,
    backwardInnerAntecedent,
  )
  const propertyBody = exactOne(
    directCuts(backward.diagram, propertyScope),
    'Nat(a) property body',
  )
  const property = relationWire(
    backward.diagram,
    propertyScope,
    UNARY,
  )
  backward.record('ground Nat(a) directly to commutativity carrier', {
    rule: 'wireJoin',
    input: {
      kind: 'relation',
      wire: property,
      content: commutativityCarrierContent(),
      parameters: [backwardPlus, backwardRight],
    },
  })
  const hereditary = exactOne(
    directCuts(backward.diagram, propertyBody),
    'Nat(a) hereditary implication',
  )
  const nestedBase = exactOne(
    directCuts(backward.diagram, hereditary).filter((region) =>
      scopedWires(backward.diagram, region).length === 1),
    'nested commutativity base',
  )
  const nestedClosure = exactOne(
    directCuts(backward.diagram, hereditary).filter((region) =>
      scopedWires(backward.diagram, region).length === 2),
    'nested commutativity closure',
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
    backward.record(`discharge Nat(a) ${label}`, {
      rule: 'deiteration',
      sel,
      justifier: evidence.justifier,
      certificate: evidence.certificate,
      retargets: [],
    })
  }
  backward.record('expose inherited commutativity carrier', {
    rule: 'doubleCutElim',
    region: hereditary,
  })
  backward.record('remove grounded Nat(a) property scope', {
    rule: 'doubleCutElim',
    region: propertyScope,
  })
  const carrierComponents = directCuts(
    backward.diagram,
    backwardInnerAntecedent,
  ).filter((region) =>
    region !== backwardInnerConsequent
    && region !== externalBase
    && region !== externalClosure)
  const inheritedCross = exactOne(
    carrierComponents.filter((region) => {
      const body = directCuts(backward.diagram, region)
      return body.length === 1
        && directCuts(backward.diagram, body[0]!).length === 1
    }),
    'inherited crossed implication',
  )
  const inheritedCrossBody = exactOne(
    directCuts(backward.diagram, inheritedCross),
    'inherited crossed body',
  )
  const inheritedCrossAntecedent = exactOne(
    directCuts(backward.diagram, inheritedCrossBody),
    'inherited crossed antecedent',
  )
  const inheritedCrossConsequent = exactOne(
    directCuts(backward.diagram, inheritedCrossAntecedent),
    'inherited crossed consequent',
  )
  backward.record('specialize crossed implication at public output', {
    rule: 'wireJoin',
    input: {
      kind: 'iota',
      a: backwardOutput,
      b: exactOne(
        scopedWires(backward.diagram, inheritedCross),
        'crossed output',
      ),
    },
  })
  deiterateNode(
    backward,
    'discharge crossed public Plus premise',
    inheritedCrossAntecedent,
    exactOne(
      directNodes(backward.diagram, inheritedCrossAntecedent),
      'crossed Plus premise',
    ),
  )
  const derivedCrossed = exactOne(
    directNodes(backward.diagram, inheritedCrossConsequent),
    'derived crossed Plus',
  )
  backward.record('expose crossed Plus', {
    rule: 'doubleCutElim',
    region: inheritedCrossAntecedent,
  })
  backward.record('remove crossed output scope', {
    rule: 'doubleCutElim',
    region: inheritedCross,
  })
  void derivedCrossed
  return {
    name: 'plusComm',
    lhs,
    rhs,
    actions: forward.actions,
    backActions: backward.actions,
  }
}

export function buildCommutativityTheorems(
  relations: Theory['relations'],
  prefix: readonly Theorem[],
  statements: ArithmeticStatements,
): readonly Theorem[] {
  let context = verifyTheory({ relations, theorems: prefix })
  const carrierInductive = commutativityCarrierInductive(
    statements,
    context,
  )
  context = registerTheorem(context, carrierInductive)
  const commutativity = plusComm(statements, context)
  context = registerTheorem(context, commutativity)
  void context
  return Object.freeze([carrierInductive, commutativity])
}
