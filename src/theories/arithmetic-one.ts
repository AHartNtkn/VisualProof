import type {
  NodeId,
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
import type { Theorem } from '../kernel/proof/theorem'
import {
  atom,
  declareWire,
  emptyGraph,
  finishDiagramWithBoundary,
  implication,
  quantifierScope,
} from './graph'
import {
  BINARY,
  UNARY,
  deiterationStep,
  directCuts,
  directNodes,
  endpointWire,
  exactOne,
  nodeWithHead,
  relationWire,
  scopedWires,
} from './arithmetic-support'
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
  const successor = declareWire(graph, graph.root, BINARY)
  graph = successor.graph

  const zeroValue = declareWire(graph, graph.root, IOTA)
  graph = zeroValue.graph
  graph = atom(graph, graph.root, zero.value, [zeroValue.value]).graph

  const total = quantifierScope(graph, graph.root, 'forall', [IOTA])
  graph = total.graph
  const totalOutput = declareWire(graph, total.value.body, IOTA)
  graph = totalOutput.graph
  graph = atom(
    graph,
    total.value.body,
    successor.value,
    [total.value.variables[0]!, totalOutput.value],
  ).graph

  return finishDiagramWithBoundary(
    graph,
    [zero.value, successor.value],
  )
}

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
  const baseClaim = implication(graph, base.value.body)
  graph = baseClaim.graph
  graph = atom(
    graph,
    baseClaim.value.antecedent,
    zero.value,
    [base.value.variables[0]!],
  ).graph
  graph = atom(
    graph,
    baseClaim.value.consequent,
    property.value,
    [base.value.variables[0]!],
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

function spawnAttached(
  recorder: PrimitiveStepRecorder,
  region: RegionId,
  head: WireId,
  args: readonly WireId[],
  label: string,
): NodeId {
  const before = recorder.diagram
  recorder.record(`insert ${label}`, {
    rule: 'atomSpawn',
    region,
    wire: head,
  })
  const node = onlyNewNode(before, recorder.diagram, region)
  args.forEach((wire, index) => {
    recorder.record(`attach ${label} argument ${index}`, {
      rule: 'wireJoin',
      input: {
        kind: 'iota',
        a: wire,
        b: endpointWire(recorder.diagram, node, 'arg', index),
      },
    })
  })
  return node
}

function buildForward(context: ProofContext) {
  const lhs = finishDiagramWithBoundary(emptyGraph(), [])
  const forward = new PrimitiveStepRecorder(lhs.diagram, context)
  let before = forward.diagram

  forward.record('open zero/successor primitive universal scope', {
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
    'primitive body',
  )

  before = forward.diagram
  forward.record('introduce theorem-local zero relation', {
    rule: 'vacuousIntro',
    scope: primitiveScope,
    sig: UNARY,
  })
  const zero = onlyNewWire(before, forward.diagram, primitiveScope)

  before = forward.diagram
  forward.record('introduce theorem-local successor relation', {
    rule: 'vacuousIntro',
    scope: primitiveScope,
    sig: BINARY,
  })
  const successor = onlyNewWire(before, forward.diagram, primitiveScope)

  before = forward.diagram
  forward.record('open exact-hypothesis implication', {
    rule: 'doubleCutIntro',
    sel: {
      region: primitiveBody,
      regions: [],
      nodes: [],
      wires: [],
    },
  })
  const antecedent = onlyNewCut(before, forward.diagram, primitiveBody)
  const conclusion = exactOne(
    directCuts(forward.diagram, antecedent),
    'theorem conclusion',
  )

  before = forward.diagram
  forward.record('introduce temporary exact hypotheses handle', {
    rule: 'vacuousIntro',
    scope: antecedent,
    sig: relSig([]),
  })
  const temporaryHypotheses = onlyNewWire(
    before,
    forward.diagram,
    antecedent,
  )
  forward.record('assert temporary exact hypotheses handle', {
    rule: 'atomSpawn',
    region: antecedent,
    wire: temporaryHypotheses,
  })
  forward.record('ground exact zeroExists and successorTotal hypotheses', {
    rule: 'wireJoin',
    input: {
      kind: 'relation',
      wire: temporaryHypotheses,
      content: exactHypothesesContent(),
      parameters: [zero, successor],
    },
  })

  const zeroAnchor = nodeWithHead(forward.diagram, antecedent, zero)
  const zeroValue = endpointWire(
    forward.diagram,
    zeroAnchor,
    'arg',
    0,
  )
  const successorAnchor = spawnAttached(
    forward,
    antecedent,
    successor,
    [zeroValue],
    'specialized successor-totality witness',
  )
  const successorValue = endpointWire(
    forward.diagram,
    successorAnchor,
    'arg',
    1,
  )

  forward.record('iterate zero witness into one-is-Nat conclusion', {
    rule: 'iteration',
    sel: {
      region: antecedent,
      regions: [],
      nodes: [zeroAnchor],
      wires: [],
    },
    target: conclusion,
    retargets: [],
  })
  forward.record('iterate successor witness into one-is-Nat conclusion', {
    rule: 'iteration',
    sel: {
      region: antecedent,
      regions: [],
      nodes: [successorAnchor],
      wires: [],
    },
    target: conclusion,
    retargets: [],
  })

  before = forward.diagram
  forward.record('open arbitrary-property universal scope', {
    rule: 'doubleCutIntro',
    sel: {
      region: conclusion,
      regions: [],
      nodes: [],
      wires: [],
    },
  })
  const propertyScope = onlyNewCut(
    before,
    forward.diagram,
    conclusion,
  )
  const propertyBody = exactOne(
    directCuts(forward.diagram, propertyScope),
    'property body',
  )

  before = forward.diagram
  forward.record('introduce arbitrary hereditary property', {
    rule: 'vacuousIntro',
    scope: propertyScope,
    sig: UNARY,
  })
  const property = onlyNewWire(
    before,
    forward.diagram,
    propertyScope,
  )

  before = forward.diagram
  forward.record('open Nat hereditary implication', {
    rule: 'doubleCutIntro',
    sel: {
      region: propertyBody,
      regions: [],
      nodes: [],
      wires: [],
    },
  })
  const hereditary = onlyNewCut(
    before,
    forward.diagram,
    propertyBody,
  )
  const inherited = exactOne(
    directCuts(forward.diagram, hereditary),
    'Nat inherited result',
  )

  before = forward.diagram
  forward.record('introduce temporary hereditary-conditions handle', {
    rule: 'vacuousIntro',
    scope: hereditary,
    sig: relSig([]),
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
  forward.record('ground exact Nat base and closure conditions', {
    rule: 'wireJoin',
    input: {
      kind: 'relation',
      wire: temporaryConditions,
      content: hereditaryConditionsContent(),
      parameters: [zero, successor, property],
    },
  })

  const propertyAtZero = spawnAttached(
    forward,
    hereditary,
    property,
    [zeroValue],
    'property consequence at zero',
  )
  const propertyAtSuccessor = spawnAttached(
    forward,
    hereditary,
    property,
    [successorValue],
    'property consequence at successor',
  )
  forward.record('iterate successor property to Nat candidate', {
    rule: 'iteration',
    sel: {
      region: hereditary,
      regions: [],
      nodes: [propertyAtSuccessor],
      wires: [],
    },
    target: inherited,
    retargets: [],
  })

  return {
    lhs,
    recorder: forward,
    propertyAtZero,
  }
}

function buildBackward(
  rhs: ReturnType<typeof finishDiagramWithBoundary>,
  context: ProofContext,
) {
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
  const antecedent = exactOne(
    directCuts(backward.diagram, primitiveBody),
    'reviewed theorem antecedent',
  )
  const antecedentChildren = directCuts(backward.diagram, antecedent)
  const totalityScope = exactOne(
    antecedentChildren.filter((region) =>
      scopedWires(backward.diagram, region).length === 1),
    'successorTotal scope',
  )
  const conclusion = exactOne(
    antecedentChildren.filter((region) => region !== totalityScope),
    'reviewed conclusion',
  )
  const zero = relationWire(backward.diagram, primitiveScope, UNARY)
  const successor = relationWire(
    backward.diagram,
    primitiveScope,
    BINARY,
  )
  const zeroAnchor = nodeWithHead(backward.diagram, antecedent, zero)
  const zeroValue = endpointWire(
    backward.diagram,
    zeroAnchor,
    'arg',
    0,
  )
  const conclusionZero = nodeWithHead(
    backward.diagram,
    conclusion,
    zero,
  )
  const conclusionSuccessor = nodeWithHead(
    backward.diagram,
    conclusion,
    successor,
  )
  const conclusionNat = exactOne(
    directNodes(backward.diagram, conclusion).filter((node) =>
      backward.diagram.nodes[node]!.kind === 'ref'),
    'one-is-Nat conclusion ref',
  )

  backward.record('identify conclusion zero with zeroExists witness', {
    rule: 'wireJoin',
    input: {
      kind: 'iota',
      a: zeroValue,
      b: endpointWire(
        backward.diagram,
        conclusionZero,
        'arg',
        0,
      ),
    },
  })

  let before = backward.diagram
  backward.record('copy successorTotal for the zero witness', {
    rule: 'iteration',
    sel: {
      region: antecedent,
      regions: [totalityScope],
      nodes: [],
      wires: [],
    },
    target: antecedent,
    retargets: [],
  })
  const copiedTotality = onlyNewCut(
    before,
    backward.diagram,
    antecedent,
  )
  const copiedTotalityBody = exactOne(
    directCuts(backward.diagram, copiedTotality),
    'copied successorTotal body',
  )
  const derivedSuccessor = nodeWithHead(
    backward.diagram,
    copiedTotalityBody,
    successor,
  )
  backward.record('specialize successorTotal at the zero witness', {
    rule: 'wireJoin',
    input: {
      kind: 'iota',
      a: zeroValue,
      b: endpointWire(
        backward.diagram,
        derivedSuccessor,
        'arg',
        0,
      ),
    },
  })
  const successorValue = endpointWire(
    backward.diagram,
    derivedSuccessor,
    'arg',
    1,
  )
  backward.record('expose successorTotal witness', {
    rule: 'doubleCutElim',
    region: copiedTotality,
  })
  backward.record('identify conclusion successor with totality witness', {
    rule: 'wireJoin',
    input: {
      kind: 'iota',
      a: successorValue,
      b: endpointWire(
        backward.diagram,
        conclusionSuccessor,
        'arg',
        1,
      ),
    },
  })

  before = backward.diagram
  backward.record('unfold one-is-Nat conclusion', {
    rule: 'unfold',
    nodeId: conclusionNat,
  })
  const propertyScope = onlyNewCut(
    before,
    backward.diagram,
    conclusion,
  )
  const propertyBody = exactOne(
    directCuts(backward.diagram, propertyScope),
    'unfolded property body',
  )
  const hereditary = exactOne(
    directCuts(backward.diagram, propertyBody),
    'unfolded hereditary antecedent',
  )
  const property = exactOne(
    scopedWires(backward.diagram, propertyScope),
    'unfolded property',
  )
  const hereditaryChildren = directCuts(backward.diagram, hereditary)
  const inherited = exactOne(
    hereditaryChildren.filter((region) =>
      scopedWires(backward.diagram, region).length === 0),
    'inherited result',
  )
  const baseCondition = exactOne(
    hereditaryChildren.filter((region) =>
      scopedWires(backward.diagram, region).length === 1),
    'Nat base condition',
  )
  const closureCondition = exactOne(
    hereditaryChildren.filter((region) =>
      scopedWires(backward.diagram, region).length === 2),
    'Nat closure condition',
  )

  before = backward.diagram
  backward.record('copy Nat base condition for specialization', {
    rule: 'iteration',
    sel: {
      region: hereditary,
      regions: [baseCondition],
      nodes: [],
      wires: [],
    },
    target: hereditary,
    retargets: [],
  })
  const copiedBase = onlyNewCut(
    before,
    backward.diagram,
    hereditary,
  )
  const copiedBaseBody = exactOne(
    directCuts(backward.diagram, copiedBase),
    'copied base body',
  )
  const copiedBaseAntecedent = exactOne(
    directCuts(backward.diagram, copiedBaseBody),
    'copied base antecedent',
  )
  const copiedBaseZero = nodeWithHead(
    backward.diagram,
    copiedBaseAntecedent,
    zero,
  )
  for (const variable of scopedWires(backward.diagram, copiedBase)) {
    backward.record('specialize Nat base at zero witness', {
      rule: 'wireJoin',
      input: { kind: 'iota', a: zeroValue, b: variable },
    })
  }
  backward.record(
    'discharge Nat base zero premise',
    deiterationStep(
      backward.diagram,
      copiedBaseAntecedent,
      copiedBaseZero,
    ),
  )
  backward.record('expose Nat base consequence', {
    rule: 'doubleCutElim',
    region: copiedBaseAntecedent,
  })
  backward.record('finish Nat base specialization', {
    rule: 'doubleCutElim',
    region: copiedBase,
  })
  const propertyAtZero = nodeWithHead(
    backward.diagram,
    hereditary,
    property,
  )

  before = backward.diagram
  backward.record('copy Nat closure condition for specialization', {
    rule: 'iteration',
    sel: {
      region: hereditary,
      regions: [closureCondition],
      nodes: [],
      wires: [],
    },
    target: hereditary,
    retargets: [],
  })
  const copiedClosure = onlyNewCut(
    before,
    backward.diagram,
    hereditary,
  )
  const copiedClosureBody = exactOne(
    directCuts(backward.diagram, copiedClosure),
    'copied closure body',
  )
  const copiedClosureAntecedent = exactOne(
    directCuts(backward.diagram, copiedClosureBody),
    'copied closure antecedent',
  )
  const copiedPropertyPremise = nodeWithHead(
    backward.diagram,
    copiedClosureAntecedent,
    property,
  )
  const copiedSuccessorPremise = nodeWithHead(
    backward.diagram,
    copiedClosureAntecedent,
    successor,
  )
  const copiedSuccessorInput = endpointWire(
    backward.diagram,
    copiedSuccessorPremise,
    'arg',
    0,
  )
  for (const variable of scopedWires(backward.diagram, copiedClosure)) {
    const target = variable === copiedSuccessorInput
      ? zeroValue
      : successorValue
    backward.record('specialize Nat closure at zero successor', {
      rule: 'wireJoin',
      input: { kind: 'iota', a: target, b: variable },
    })
  }
  backward.record(
    'discharge Nat closure property premise',
    deiterationStep(
      backward.diagram,
      copiedClosureAntecedent,
      copiedPropertyPremise,
    ),
  )
  backward.record(
    'discharge Nat closure successor premise',
    deiterationStep(
      backward.diagram,
      copiedClosureAntecedent,
      copiedSuccessorPremise,
    ),
  )
  backward.record('expose Nat closure consequence', {
    rule: 'doubleCutElim',
    region: copiedClosureAntecedent,
  })
  backward.record('finish Nat closure specialization', {
    rule: 'doubleCutElim',
    region: copiedClosure,
  })

  if (
    backward.diagram.nodes[propertyAtZero] === undefined
    || directNodes(backward.diagram, inherited).length !== 1
  ) {
    throw new Error('Nat specialization lost required property evidence')
  }

  return { recorder: backward }
}

function oneIsNat(
  statements: ArithmeticStatements,
  context: ProofContext,
): Theorem {
  const forward = buildForward(context)
  const rhs = statements.oneIsNat
  const backward = buildBackward(rhs, context)
  return {
    name: 'oneIsNat',
    lhs: forward.lhs,
    rhs,
    actions: forward.recorder.actions,
    backActions: backward.recorder.actions,
  }
}

export function buildOneTheorem(
  relations: Theory['relations'],
  prefix: readonly Theorem[],
  statements: ArithmeticStatements,
): readonly Theorem[] {
  const context = verifyTheory({ relations, theorems: prefix })
  const one = oneIsNat(statements, context)
  registerTheorem(context, one)
  return Object.freeze([one])
}
