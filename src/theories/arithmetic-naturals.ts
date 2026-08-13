import type {
  Diagram,
  RegionId,
  WireId,
} from '../kernel/diagram/diagram'
import { IOTA, relSig } from '../kernel/diagram/sig'
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
  UNARY,
  deiterationStep,
  directCuts,
  directNodes,
  endpointWire,
  exactOne,
  introducedContentSelection,
  natHereditaryParts,
  nodeWithHead,
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
import { natRelation } from './naturals'
import type { ArithmeticStatements } from './statements'

function hereditaryConditionsContent() {
  let graph = emptyGraph()
  const zero = declareWire(graph, graph.root, UNARY)
  graph = zero.graph
  const successor = declareWire(graph, graph.root, BINARY)
  graph = successor.graph
  const property = declareWire(graph, graph.root, UNARY)
  graph = property.graph

  const base = quantifierScope(graph, graph.root, 'forall', [IOTA])
  graph = base.graph
  const zeroValue = base.value.variables[0]!
  const baseClaim = implication(graph, base.value.body)
  graph = baseClaim.graph
  graph = atom(
    graph,
    baseClaim.value.antecedent,
    zero.value,
    [zeroValue],
  ).graph
  graph = atom(
    graph,
    baseClaim.value.consequent,
    property.value,
    [zeroValue],
  ).graph

  const closure = quantifierScope(
    graph,
    graph.root,
    'forall',
    [IOTA, IOTA],
  )
  graph = closure.graph
  const [predecessor, successorValue] = closure.value.variables
  const closureClaim = implication(graph, closure.value.body)
  graph = closureClaim.graph
  graph = atom(
    graph,
    closureClaim.value.antecedent,
    property.value,
    [predecessor!],
  ).graph
  graph = atom(
    graph,
    closureClaim.value.antecedent,
    successor.value,
    [predecessor!, successorValue!],
  ).graph
  graph = atom(
    graph,
    closureClaim.value.consequent,
    property.value,
    [successorValue!],
  ).graph

  return finishDiagramWithBoundary(
    graph,
    [zero.value, successor.value, property.value],
  )
}

function buildZeroForward(context: ProofContext) {
  const lhs = finishDiagramWithBoundary(emptyGraph(), [])
  const forward = new PrimitiveStepRecorder(lhs, context)

  let before = forward.diagram
  forward.record('open primitive universal scope', {
    rule: 'doubleCutIntro',
    sel: { region: forward.diagram.root, regions: [], nodes: [], wires: [] },
  })
  const primitiveScope = onlyNewCut(before, forward.diagram, forward.diagram.root)
  const primitiveBody = exactOne(
    directCuts(forward.diagram, primitiveScope),
    'primitive universal body',
  )

  before = forward.diagram
  forward.record('introduce theorem-local zero relation', {
    rule: 'vacuity',
    direction: 'insert',
    assembly: bareWireAssembly('zero', primitiveScope, UNARY),
  })
  const zero = onlyNewWire(before, forward.diagram, primitiveScope)

  before = forward.diagram
  forward.record('introduce theorem-local successor relation', {
    rule: 'vacuity',
    direction: 'insert',
    assembly: bareWireAssembly('successor', primitiveScope, BINARY),
  })
  const successor = onlyNewWire(before, forward.diagram, primitiveScope)

  before = forward.diagram
  forward.record('open theorem implication', {
    rule: 'doubleCutIntro',
    sel: { region: primitiveBody, regions: [], nodes: [], wires: [] },
  })
  const antecedent = onlyNewCut(before, forward.diagram, primitiveBody)
  const conclusion = exactOne(
    directCuts(forward.diagram, antecedent),
    'theorem conclusion',
  )

  before = forward.diagram
  forward.record('insert existential zero witness', {
    rule: 'atomSpawn',
    region: antecedent,
    wire: zero,
  })
  const zeroAnchor = onlyNewNode(before, forward.diagram, antecedent)
  const zeroValue = endpointWire(forward.diagram, zeroAnchor, 'arg', 0)

  forward.record('iterate zero evidence into existential conclusion', {
    rule: 'iteration',
    sel: { region: antecedent, regions: [], nodes: [zeroAnchor], wires: [] },
    target: conclusion,
  })

  before = forward.diagram
  forward.record('open arbitrary-property universal scope', {
    rule: 'doubleCutIntro',
    sel: { region: conclusion, regions: [], nodes: [], wires: [] },
  })
  const propertyScope = onlyNewCut(before, forward.diagram, conclusion)
  const propertyBody = exactOne(
    directCuts(forward.diagram, propertyScope),
    'property universal body',
  )
  before = forward.diagram
  forward.record('introduce arbitrary property', {
    rule: 'vacuity',
    direction: 'insert',
    assembly: bareWireAssembly('property', propertyScope, UNARY),
  })
  const property = onlyNewWire(before, forward.diagram, propertyScope)

  before = forward.diagram
  forward.record('open hereditary implication', {
    rule: 'doubleCutIntro',
    sel: { region: propertyBody, regions: [], nodes: [], wires: [] },
  })
  const hereditary = onlyNewCut(before, forward.diagram, propertyBody)
  const inherited = exactOne(
    directCuts(forward.diagram, hereditary),
    'hereditary result',
  )

  before = forward.diagram
  forward.record('introduce temporary hereditary-conditions handle', {
    rule: 'vacuity',
    direction: 'insert',
    assembly: bareWireAssembly('temporaryConditions', hereditary, relSig([])),
  })
  const temporaryConditions = onlyNewWire(
    before,
    forward.diagram,
    hereditary,
  )
  forward.record('assert temporary hereditary-conditions handle', {
    rule: 'atomSpawn',
    region: hereditary,
    wire: temporaryConditions,
  })
  forward.recordRelationJoin('ground exact Nat base and closure conditions', {
    wire: temporaryConditions,
      content: hereditaryConditionsContent(),
      parameters: [zero, successor, property],
  })

  before = forward.diagram
  forward.record('insert property at zero as base consequence', {
    rule: 'atomSpawn',
    region: hereditary,
    wire: property,
  })
  const propertyAtZero = onlyNewNode(before, forward.diagram, hereditary)
  forward.record('identify base consequence with zero witness', {
    rule: 'wireJoin',
    input: {
      a: zeroValue,
      b: endpointWire(forward.diagram, propertyAtZero, 'arg', 0),
    },
  })

  forward.record('iterate base consequence to Nat candidate', {
    rule: 'iteration',
    sel: {
      region: hereditary,
      regions: [],
      nodes: [propertyAtZero],
      wires: [],
    },
    target: inherited,
  })

  return { recorder: forward }
}

function buildZeroBackward(
  rhs: ReturnType<typeof finishDiagramWithBoundary>,
  context: ProofContext,
) {
  const backward = new PrimitiveStepRecorder(rhs, context, 'backward')
  const primitiveScope = exactOne(
    directCuts(backward.diagram, backward.diagram.root),
    'reviewed primitive scope',
  )
  const primitiveBody = exactOne(
    directCuts(backward.diagram, primitiveScope),
    'reviewed primitive body',
  )
  const antecedent = exactOne(
    directCuts(backward.diagram, primitiveBody),
    'reviewed theorem antecedent',
  )
  const conclusion = exactOne(
    directCuts(backward.diagram, antecedent),
    'reviewed theorem conclusion',
  )
  const reviewedZero = relationWire(backward.diagram, primitiveScope, UNARY)
  const existingZero = nodeWithHead(backward.diagram, antecedent, reviewedZero)
  const existingZeroWire = endpointWire(
    backward.diagram,
    existingZero,
    'arg',
    0,
  )
  const conclusionNodes = directNodes(backward.diagram, conclusion)
  const conclusionZero = exactOne(
    conclusionNodes.filter((node) =>
      backward.diagram.nodes[node]!.kind === 'atom'),
    'zero conclusion atom',
  )
  const conclusionNat = exactOne(
    conclusionNodes.filter((node) =>
      backward.diagram.nodes[node]!.kind === 'ref'),
    'Nat conclusion ref',
  )
  backward.record('identify conclusion witness with antecedent zero', {
    rule: 'wireJoin',
    input: {
      a: existingZeroWire,
      b: endpointWire(backward.diagram, conclusionZero, 'arg', 0),
    },
  })

  let before = backward.diagram
  backward.record('unfold parameterized Nat', {
    rule: 'unfold',
    nodeId: conclusionNat,
  })
  const propertyScope = onlyNewCut(before, backward.diagram, conclusion)
  const propertyBody = exactOne(
    directCuts(backward.diagram, propertyScope),
    'unfolded property body',
  )
  const unfoldedHereditary = exactOne(
    directCuts(backward.diagram, propertyBody),
    'unfolded hereditary antecedent',
  )
  const { baseCondition } = natHereditaryParts(
    backward.diagram,
    unfoldedHereditary,
  )

  before = backward.diagram
  backward.record('copy Nat base condition for specialization', {
    rule: 'iteration',
    sel: {
      region: unfoldedHereditary,
      regions: [baseCondition],
      nodes: [],
      wires: [],
    },
    target: unfoldedHereditary,
  })
  const specializedBaseCondition = onlyNewCut(
    before,
    backward.diagram,
    unfoldedHereditary,
  )

  const baseBody = exactOne(
    directCuts(backward.diagram, specializedBaseCondition),
    'base universal body',
  )
  const baseAntecedent = exactOne(
    directCuts(backward.diagram, baseBody),
    'base implication antecedent',
  )
  const baseZero = nodeWithHead(
    backward.diagram,
    baseAntecedent,
    reviewedZero,
  )
  for (const variable of scopedWires(
    backward.diagram,
    specializedBaseCondition,
  )) {
    backward.record('specialize Nat base at zero witness', {
      rule: 'wireJoin',
      input: { a: existingZeroWire, b: variable },
    })
  }
  backward.record(
    'discharge Nat base zero premise',
    deiterationStep(backward.diagram, baseAntecedent, baseZero),
  )
  backward.record('expose Nat base consequence', {
    rule: 'doubleCutElim',
    region: baseAntecedent,
  })
  backward.record('finish Nat base specialization', {
    rule: 'doubleCutElim',
    region: specializedBaseCondition,
  })

  return { recorder: backward }
}

type MeetingParts = {
  readonly propertyScope: RegionId
  readonly hereditary: RegionId
  readonly inherited: RegionId
  readonly baseCondition: RegionId
  readonly closureCondition: RegionId
}

type ForwardResult = {
  readonly lhs: ReturnType<typeof finishDiagramWithBoundary>
  readonly recorder: PrimitiveStepRecorder
  readonly meeting: MeetingParts
}

type BackwardResult = {
  readonly recorder: PrimitiveStepRecorder
  readonly meeting: MeetingParts
  readonly theoremAntecedent: RegionId
  readonly claimAntecedent: RegionId
  readonly primitiveScope: RegionId
}

function meetingParts(
  diagram: Diagram,
  claimConsequent: RegionId,
): MeetingParts {
  const propertyScope = exactOne(
    directCuts(diagram, claimConsequent),
    'unfolded arbitrary-property scope',
  )
  const propertyBody = exactOne(
    directCuts(diagram, propertyScope),
    'unfolded arbitrary-property body',
  )
  const hereditary = exactOne(
    directCuts(diagram, propertyBody),
    'unfolded hereditary antecedent',
  )
  const {
    inherited,
    baseCondition,
    closureCondition,
  } = natHereditaryParts(diagram, hereditary)
  return {
    propertyScope,
    hereditary,
    inherited,
    baseCondition,
    closureCondition,
  }
}

function buildSuccForward(context: ProofContext): ForwardResult {
  const lhs = finishDiagramWithBoundary(emptyGraph(), [])
  const forward = new PrimitiveStepRecorder(lhs, context)

  let before = forward.diagram
  forward.record('open primitive universal scope', {
    rule: 'doubleCutIntro',
    sel: {
      region: forward.diagram.root,
      regions: [],
      nodes: [],
      wires: [],
    },
  })
  const primitiveScope = onlyNewCut(
    before,
    forward.diagram,
    forward.diagram.root,
  )
  const primitiveBody = exactOne(
    directCuts(forward.diagram, primitiveScope),
    'primitive universal body',
  )

  before = forward.diagram
  forward.record('introduce theorem-local zero relation', {
    rule: 'vacuity',
    direction: 'insert',
    assembly: bareWireAssembly('zero', primitiveScope, UNARY),
  })
  const zero = onlyNewWire(before, forward.diagram, primitiveScope)

  before = forward.diagram
  forward.record('introduce theorem-local successor relation', {
    rule: 'vacuity',
    direction: 'insert',
    assembly: bareWireAssembly('successor', primitiveScope, BINARY),
  })
  const successor = onlyNewWire(before, forward.diagram, primitiveScope)

  before = forward.diagram
  forward.record('open exact empty-hypothesis theorem implication', {
    rule: 'doubleCutIntro',
    sel: {
      region: primitiveBody,
      regions: [],
      nodes: [],
      wires: [],
    },
  })
  const theoremAntecedent = onlyNewCut(
    before,
    forward.diagram,
    primitiveBody,
  )
  const theoremConclusion = exactOne(
    directCuts(forward.diagram, theoremAntecedent),
    'theorem conclusion',
  )

  before = forward.diagram
  forward.record('open successor-closure universal scope', {
    rule: 'doubleCutIntro',
    sel: {
      region: theoremConclusion,
      regions: [],
      nodes: [],
      wires: [],
    },
  })
  const claimScope = onlyNewCut(
    before,
    forward.diagram,
    theoremConclusion,
  )
  const claimBody = exactOne(
    directCuts(forward.diagram, claimScope),
    'successor-closure universal body',
  )

  const claimVariables: WireId[] = []
  for (const label of ['predecessor', 'successor']) {
    before = forward.diagram
    forward.record(`introduce successor-closure ${label}`, {
      rule: 'vacuity',
      direction: 'insert',
      assembly: bareWireAssembly('claimVariable', claimScope, IOTA),
    })
    claimVariables.push(onlyNewWire(before, forward.diagram, claimScope))
  }
  const [predecessor, successorResult] = claimVariables as [
    WireId,
    WireId,
  ]

  before = forward.diagram
  forward.record('open successor-closure implication', {
    rule: 'doubleCutIntro',
    sel: {
      region: claimBody,
      regions: [],
      nodes: [],
      wires: [],
    },
  })
  const claimAntecedent = onlyNewCut(
    before,
    forward.diagram,
    claimBody,
  )
  const claimConsequent = exactOne(
    directCuts(forward.diagram, claimAntecedent),
    'successor-closure consequent',
  )

  before = forward.diagram
  forward.record('introduce temporary predecessor-Nat proposition', {
    rule: 'vacuity',
    direction: 'insert',
    assembly: bareWireAssembly('temporaryNat', claimAntecedent, { kind: 'rel', args: [] }),
  })
  const temporaryNat = onlyNewWire(
    before,
    forward.diagram,
    claimAntecedent,
  )

  forward.record('assert temporary predecessor-Nat proposition', {
    rule: 'atomSpawn',
    region: claimAntecedent,
    wire: temporaryNat,
  })

  before = forward.diagram
  forward.recordRelationJoin('ground predecessor Nat on supplied primitives', {
    wire: temporaryNat,
      content: natRelation(),
      parameters: [zero, successor, predecessor],
  })
  const predecessorNatMaterial = introducedContentSelection(
    before,
    forward.diagram,
    claimAntecedent,
  )

  before = forward.diagram
  forward.record('fold grounded predecessor Nat premise', {
    rule: 'fold',
    occurrence: predecessorNatMaterial,
    args: [zero, successor, predecessor],
    defId: 'nat',
  })
  const predecessorNat = onlyNewNode(
    before,
    forward.diagram,
    claimAntecedent,
  )

  before = forward.diagram
  forward.record('insert supplied successor premise', {
    rule: 'atomSpawn',
    region: claimAntecedent,
    wire: successor,
  })
  const successorPremise = onlyNewNode(
    before,
    forward.diagram,
    claimAntecedent,
  )
  forward.record('attach supplied successor predecessor', {
    rule: 'wireJoin',
    input: {
      a: predecessor,
      b: endpointWire(forward.diagram, successorPremise, 'arg', 0),
    },
  })
  forward.record('attach supplied successor result', {
    rule: 'wireJoin',
    input: {
      a: successorResult,
      b: endpointWire(forward.diagram, successorPremise, 'arg', 1),
    },
  })

  before = forward.diagram
  forward.record('iterate explicit predecessor Nat into conclusion', {
    rule: 'iteration',
    sel: {
      region: claimAntecedent,
      regions: [],
      nodes: [predecessorNat],
      wires: [],
    },
    target: claimConsequent,
  })
  const copiedNat = onlyNewNode(
    before,
    forward.diagram,
    claimConsequent,
  )

  before = forward.diagram
  forward.record('unfold copied predecessor Nat', {
    rule: 'unfold',
    nodeId: copiedNat,
  })
  const meeting = meetingParts(forward.diagram, claimConsequent)
  const property = exactOne(
    scopedWires(forward.diagram, meeting.propertyScope),
    'unfolded arbitrary property wire',
  )
  const predecessorProperty = nodeWithHead(
    forward.diagram,
    meeting.inherited,
    property,
  )

  before = forward.diagram
  forward.record('copy full hereditary closure for specialization', {
    rule: 'iteration',
    sel: {
      region: meeting.hereditary,
      regions: [meeting.closureCondition],
      nodes: [],
      wires: [],
    },
    target: meeting.inherited,
  })
  const copiedClosureScope = onlyNewCut(
    before,
    forward.diagram,
    meeting.inherited,
  )
  const copiedClosureBody = exactOne(
    directCuts(forward.diagram, copiedClosureScope),
    'copied closure body',
  )
  const copiedClosureAntecedent = exactOne(
    directCuts(forward.diagram, copiedClosureBody),
    'copied closure antecedent',
  )
  const copiedClosureConsequent = exactOne(
    directCuts(forward.diagram, copiedClosureAntecedent),
    'copied closure consequent',
  )
  const copiedPropertyPremise = nodeWithHead(
    forward.diagram,
    copiedClosureAntecedent,
    property,
  )
  const copiedSuccessorPremise = nodeWithHead(
    forward.diagram,
    copiedClosureAntecedent,
    successor,
  )
  const successorProperty = nodeWithHead(
    forward.diagram,
    copiedClosureConsequent,
    property,
  )
  const copiedClosureInput = endpointWire(
    forward.diagram,
    copiedSuccessorPremise,
    'arg',
    0,
  )

  for (const variable of scopedWires(
    forward.diagram,
    copiedClosureScope,
  )) {
    const target = variable === copiedClosureInput
      ? predecessor
      : successorResult
    forward.record('specialize copied hereditary closure', {
      rule: 'wireJoin',
      input: {
        a: target,
        b: variable,
      },
    })
  }

  forward.record(
    'discharge copied predecessor-property premise',
    deiterationStep(
      forward.diagram,
      copiedClosureAntecedent,
      copiedPropertyPremise,
    ),
  )
  forward.record(
    'discharge copied supplied-successor premise',
    deiterationStep(
      forward.diagram,
      copiedClosureAntecedent,
      copiedSuccessorPremise,
    ),
  )
  forward.record('expose copied successor-property result', {
    rule: 'doubleCutElim',
    region: copiedClosureAntecedent,
  })
  forward.record('finish copied hereditary-closure specialization', {
    rule: 'doubleCutElim',
    region: copiedClosureScope,
  })
  forward.record('erase obsolete predecessor-property result', {
    rule: 'erasure',
    sel: {
      region: meeting.inherited,
      regions: [],
      nodes: [predecessorProperty],
      wires: [],
    },
  })
  if (forward.diagram.nodes[successorProperty] === undefined) {
    throw new Error('derived successor-property result disappeared')
  }

  if (
    directNodes(forward.diagram, theoremAntecedent).length !== 0
    || scopedWires(forward.diagram, theoremAntecedent).length !== 0
  ) {
    throw new Error('outer theorem antecedent is not empty')
  }

  return {
    lhs,
    recorder: forward,
    meeting: meetingParts(forward.diagram, claimConsequent),
  }
}

function buildSuccBackward(
  rhs: ReturnType<typeof finishDiagramWithBoundary>,
  context: ProofContext,
): BackwardResult {
  const backward = new PrimitiveStepRecorder(
    rhs,
    context,
    'backward',
  )
  const primitiveScope = exactOne(
    directCuts(backward.diagram, backward.diagram.root),
    'authoritative primitive scope',
  )
  const primitiveBody = exactOne(
    directCuts(backward.diagram, primitiveScope),
    'authoritative primitive body',
  )
  const theoremAntecedent = exactOne(
    directCuts(backward.diagram, primitiveBody),
    'authoritative empty theorem antecedent',
  )
  const theoremConclusion = exactOne(
    directCuts(backward.diagram, theoremAntecedent),
    'authoritative theorem conclusion',
  )
  const claimScope = exactOne(
    directCuts(backward.diagram, theoremConclusion),
    'authoritative claim scope',
  )
  const claimBody = exactOne(
    directCuts(backward.diagram, claimScope),
    'authoritative claim body',
  )
  const claimAntecedent = exactOne(
    directCuts(backward.diagram, claimBody),
    'authoritative claim antecedent',
  )
  const claimConsequent = exactOne(
    directCuts(backward.diagram, claimAntecedent),
    'authoritative claim consequent',
  )
  const consequenceNat = exactOne(
    directNodes(backward.diagram, claimConsequent),
    'authoritative successor Nat reference',
  )
  if (backward.diagram.nodes[consequenceNat]!.kind !== 'ref') {
    throw new Error('authoritative conclusion is not a Nat reference')
  }

  backward.record('unfold authoritative successor Nat conclusion', {
    rule: 'unfold',
    nodeId: consequenceNat,
  })

  if (
    directNodes(backward.diagram, theoremAntecedent).length !== 0
    || scopedWires(backward.diagram, theoremAntecedent).length !== 0
  ) {
    throw new Error('authoritative outer theorem antecedent is not empty')
  }

  return {
    recorder: backward,
    meeting: meetingParts(backward.diagram, claimConsequent),
    theoremAntecedent,
    claimAntecedent,
    primitiveScope,
  }
}

function zeroIsNat(
  statements: ArithmeticStatements,
  context: ProofContext,
): Theorem {
  const lhs = finishDiagramWithBoundary(emptyGraph(), [])
  const forward = buildZeroForward(context)
  const rhs = statements.zeroIsNat
  const backward = buildZeroBackward(rhs, context)
  return {
    name: 'zeroIsNat',
    lhs,
    rhs,
    actions: forward.recorder.actions,
    backActions: backward.recorder.actions,
  }
}

function succNat(
  statements: ArithmeticStatements,
  context: ProofContext,
): Theorem {
  const forward = buildSuccForward(context)
  const rhs = statements.succNat
  const backward = buildSuccBackward(rhs, context)
  return {
    name: 'succNat',
    lhs: forward.lhs,
    rhs,
    actions: forward.recorder.actions,
    backActions: backward.recorder.actions,
  }
}

export function buildNaturalBaseTheorems(
  relations: Theory['relations'],
  prefix: readonly Theorem[],
  statements: ArithmeticStatements,
): readonly Theorem[] {
  let context = verifyTheory({ relations, theorems: prefix })
  const zero = zeroIsNat(statements, context)
  context = registerTheorem(context, zero)
  const successor = succNat(statements, context)
  context = registerTheorem(context, successor)
  void context
  return Object.freeze([zero, successor])
}
