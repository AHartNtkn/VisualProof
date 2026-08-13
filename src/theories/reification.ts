import type { DiagramWithBoundary } from '../kernel/diagram/boundary'
import type {
  Diagram,
  NodeId,
  RegionId,
  WireId,
} from '../kernel/diagram/diagram'
import { exploreForm } from '../kernel/diagram/canonical/explore'
import { derivedScope } from '../kernel/diagram/regions'
import { IOTA, relSig, type Sig } from '../kernel/diagram/sig'
import { extractSubgraph } from '../kernel/diagram/subgraph/extract'
import { verifyTheory } from '../kernel/proof/context'
import { bareWireAssembly } from '../kernel/rules/identity-rules'
import type { Theorem } from '../kernel/proof/theorem'
import {
  atom,
  biconditional,
  declareWire,
  emptyGraph,
  finishDiagramWithBoundary,
  implication,
  quantifierScope,
  type GraphConstruction,
} from './graph'
import {
  PrimitiveStepRecorder,
  onlyNewCut,
  onlyNewNode,
  onlyNewWire,
} from './record'

const PROPOSITION = relSig([])
const UNARY = relSig([IOTA])
const BINARY = relSig([IOTA, IOTA])
const TERNARY = relSig([IOTA, IOTA, IOTA])

type UnaryMaterialDrawer = (
  graph: GraphConstruction,
  region: RegionId,
  variable: WireId,
  captures: readonly WireId[],
) => GraphConstruction

type UniversalScope = {
  readonly scope: RegionId
  readonly body: RegionId
  readonly variables: readonly WireId[]
}

type ExplicitReificationInput = {
  readonly name: string
  readonly lhs: DiagramWithBoundary
  readonly recorder: PrimitiveStepRecorder
  readonly witnessScope: RegionId
  readonly formalSignatures: readonly Sig[]
  readonly material: DiagramWithBoundary
  readonly parameters: readonly WireId[]
  readonly rhs: DiagramWithBoundary
}

function directCuts(
  diagram: Diagram,
  parent: RegionId,
): readonly RegionId[] {
  return Object.entries(diagram.regions)
    .filter(([, region]) =>
      region.kind === 'cut' && region.parent === parent)
    .map(([id]) => id)
    .sort()
}

function directNodes(
  diagram: Diagram,
  region: RegionId,
): readonly NodeId[] {
  return Object.entries(diagram.nodes)
    .filter(([, node]) => node.region === region)
    .map(([id]) => id)
    .sort()
}

function exactOne<T>(
  values: readonly T[],
  what: string,
): T {
  if (values.length !== 1) {
    throw new Error(`expected exactly one ${what}, found ${values.length}`)
  }
  return values[0]!
}

function newWires(
  before: Diagram,
  after: Diagram,
  scope: RegionId,
): readonly WireId[] {
  return Object.entries(after.wires)
    .filter(([id]) =>
      before.wires[id] === undefined && derivedScope(after, id) === scope)
    .map(([id]) => id)
    .sort()
}

function introducedContentSelection(
  before: Diagram,
  after: Diagram,
  region: RegionId,
) {
  return {
    region,
    regions: directCuts(after, region)
      .filter((id) => before.regions[id] === undefined),
    nodes: directNodes(after, region)
      .filter((id) => before.nodes[id] === undefined),
    wires: newWires(before, after, region),
  }
}

function completeRegionSelection(
  diagram: Diagram,
  region: RegionId,
) {
  return {
    region,
    regions: directCuts(diagram, region),
    nodes: directNodes(diagram, region),
    wires: Object.keys(diagram.wires)
      .filter((id) => derivedScope(diagram, id) === region)
      .sort(),
  }
}

function selectedChildForm(
  diagram: Diagram,
  parent: RegionId,
  child: RegionId,
): string {
  const extracted = extractSubgraph(diagram, {
    region: parent,
    regions: [child],
    nodes: [],
    wires: [],
  })
  return exploreForm(
    extracted.pattern.diagram,
    extracted.pattern.boundary,
  )
}

function copiedChild(
  diagram: Diagram,
  sourceParent: RegionId,
  sourceChild: RegionId,
  targetParent: RegionId,
): RegionId {
  const expected = selectedChildForm(diagram, sourceParent, sourceChild)
  return exactOne(
    directCuts(diagram, targetParent)
      .filter((candidate) =>
        selectedChildForm(diagram, targetParent, candidate) === expected),
    'copied implication consequent',
  )
}

function openUniversal(
  recorder: PrimitiveStepRecorder,
  parent: RegionId,
  signatures: readonly Sig[],
  label: string,
): UniversalScope {
  if (signatures.length === 0) {
    return {
      scope: parent,
      body: parent,
      variables: [],
    }
  }

  const before = recorder.diagram
  recorder.record(`open ${label} universal scope`, {
    rule: 'doubleCutIntro',
    sel: {
      region: parent,
      regions: [],
      nodes: [],
      wires: [],
    },
  })
  const scope = onlyNewCut(before, recorder.diagram, parent)
  const body = exactOne(
    directCuts(recorder.diagram, scope),
    `${label} universal body`,
  )
  const variables: WireId[] = []
  for (const [index, signature] of signatures.entries()) {
    const beforeVariable = recorder.diagram
    recorder.record(`introduce ${label} variable ${index + 1}`, {
      rule: 'vacuity',
      direction: 'insert',
      assembly: bareWireAssembly('universalVariable', scope, signature),
    })
    variables.push(
      onlyNewWire(beforeVariable, recorder.diagram, scope),
    )
  }
  return { scope, body, variables }
}

function insertExplicitMaterial(
  recorder: PrimitiveStepRecorder,
  region: RegionId,
  formalVariables: readonly WireId[],
  formalSignatures: readonly Sig[],
  material: DiagramWithBoundary,
  parameters: readonly WireId[],
) {
  let before = recorder.diagram
  recorder.record('introduce a temporary material relation', {
    rule: 'vacuity',
    direction: 'insert',
    assembly: bareWireAssembly(
      'temporaryMaterial',
      region,
      relSig(formalSignatures),
    ),
  })
  const temporary = onlyNewWire(before, recorder.diagram, region)

  before = recorder.diagram
  recorder.record('insert one temporary material application', {
    rule: 'atomSpawn',
    region,
    wire: temporary,
  })
  onlyNewNode(before, recorder.diagram, region)
  const localArguments = newWires(before, recorder.diagram, region)
  if (localArguments.length !== formalVariables.length) {
    throw new Error(
      `expected ${formalVariables.length} temporary formal wires, `
      + `found ${localArguments.length}`,
    )
  }
  localArguments.forEach((local, index) => {
    recorder.record(`connect material formal ${index + 1}`, {
      rule: 'wireJoin',
      input: {
        a: formalVariables[index]!,
        b: local,
      },
    })
  })

  before = recorder.diagram
  const applicationEnds = before.wires[temporary]!.endpoints
    .map((endpoint) => endpoint.node)
  recorder.recordRelationJoin('ground the temporary relation with explicit material', {
    wire: temporary,
      content: material,
      parameters,
  })
  // The compiled grounding may satisfy the material by re-heading the
  // spawned application atoms rather than splicing fresh copies, so the
  // material occurrence is the introduced content plus those survivors.
  const introduced = introducedContentSelection(before, recorder.diagram, region)
  const survivors = applicationEnds.filter((node) =>
    recorder.diagram.nodes[node]?.region === region
    && !introduced.nodes.includes(node))
  return {
    ...introduced,
    nodes: [...introduced.nodes, ...survivors].sort(),
  }
}

const explicitMaterials = new WeakMap<Theorem, DiagramWithBoundary>()

/** The material diagram one reification theorem actually grounded. */
export function explicitMaterialOf(theorem: Theorem): DiagramWithBoundary {
  const material = explicitMaterials.get(theorem)
  if (material === undefined) {
    throw new Error(`no explicit material recorded for '${theorem.name}'`)
  }
  return material
}

function recordExplicitReification(
  input: ExplicitReificationInput,
): Theorem {
  const {
    name,
    lhs,
    recorder,
    witnessScope,
    formalSignatures,
    material,
    parameters,
    rhs,
  } = input
  const universal = openUniversal(
    recorder,
    witnessScope,
    formalSignatures,
    'material',
  )

  let before = recorder.diagram
  recorder.record('open the first self-implication', {
    rule: 'doubleCutIntro',
    sel: {
      region: universal.body,
      regions: [],
      nodes: [],
      wires: [],
    },
  })
  const forward = onlyNewCut(before, recorder.diagram, universal.body)
  const forwardConsequent = exactOne(
    directCuts(recorder.diagram, forward),
    'first implication consequent',
  )

  const source = insertExplicitMaterial(
    recorder,
    forward,
    universal.variables,
    formalSignatures,
    material,
    parameters,
  )
  recorder.record('iterate the exact material into the first consequent', {
    rule: 'iteration',
    sel: source,
    target: forwardConsequent,
  })

  before = recorder.diagram
  recorder.record('iterate the complete implication as its reverse twin', {
    rule: 'iteration',
    sel: {
      region: universal.body,
      regions: [forward],
      nodes: [],
      wires: [],
    },
    target: universal.body,
  })
  const reverse = onlyNewCut(before, recorder.diagram, universal.body)
  const reverseConsequent = copiedChild(
    recorder.diagram,
    forward,
    forwardConsequent,
    reverse,
  )

  recorder.recordRelationSever('sever exact copies into one fresh relation witness', {
    scope: witnessScope,
      occurrences: [
        {
          sel: source,
          args: universal.variables,
        },
        {
          sel: completeRegionSelection(
            recorder.diagram,
            reverseConsequent,
          ),
          args: universal.variables,
        },
      ],
  })

  const theorem = {
    name,
    lhs,
    rhs,
    actions: recorder.actions,
  }
  explicitMaterials.set(theorem, material)
  return theorem
}

function captureOnly(
  signatures: readonly Sig[],
) {
  let graph = emptyGraph()
  const captures: WireId[] = []
  for (const signature of signatures) {
    const capture = declareWire(graph, graph.root, signature)
    graph = capture.graph
    captures.push(capture.value)
  }
  return {
    graph,
    captures,
    boundary: finishDiagramWithBoundary(graph, captures),
  }
}

function unaryMaterial(
  captureSignatures: readonly Sig[],
  draw: UnaryMaterialDrawer,
): DiagramWithBoundary {
  let graph = emptyGraph()
  const formal = declareWire(graph, graph.root, IOTA)
  graph = formal.graph
  const captures: WireId[] = []
  for (const signature of captureSignatures) {
    const capture = declareWire(graph, graph.root, signature)
    graph = capture.graph
    captures.push(capture.value)
  }
  graph = draw(graph, graph.root, formal.value, captures)
  return finishDiagramWithBoundary(
    graph,
    [formal.value, ...captures],
  )
}

function unaryReificationRhs(
  captureSignatures: readonly Sig[],
  draw: UnaryMaterialDrawer,
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
  graph = draw(
    graph,
    iff.value.forward.consequent,
    variable,
    captures,
  )
  graph = draw(
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

function recordedUnaryReification(
  name: string,
  captureSignatures: readonly Sig[],
  draw: UnaryMaterialDrawer,
): Theorem {
  const start = captureOnly(captureSignatures)
  const recorder = new PrimitiveStepRecorder(
    start.boundary.diagram,
    verifyTheory({ relations: [], theorems: [] }),
  )
  return recordExplicitReification({
    name,
    lhs: start.boundary,
    recorder,
    witnessScope: start.boundary.diagram.root,
    formalSignatures: [IOTA],
    material: unaryMaterial(captureSignatures, draw),
    parameters: start.captures,
    rhs: unaryReificationRhs(captureSignatures, draw),
  })
}

function drawRelationIdentityMaterial(
  graph: GraphConstruction,
  region: RegionId,
  variable: WireId,
  captures: readonly WireId[],
): GraphConstruction {
  return atom(graph, region, captures[0]!, [variable]).graph
}

function relationIdentityRhs(): DiagramWithBoundary {
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

export function relationIdentityReification(): Theorem {
  const blank = emptyGraph()
  const lhs = finishDiagramWithBoundary(blank, [])
  const recorder = new PrimitiveStepRecorder(
    lhs.diagram,
    verifyTheory({ relations: [], theorems: [] }),
  )
  const relationUniversal = openUniversal(
    recorder,
    recorder.diagram.root,
    [UNARY],
    'source relation',
  )
  const source = relationUniversal.variables[0]!
  return recordExplicitReification({
    name: 'relationIdentityReification',
    lhs,
    recorder,
    witnessScope: relationUniversal.body,
    formalSignatures: [IOTA],
    material: unaryMaterial([UNARY], drawRelationIdentityMaterial),
    parameters: [source],
    rhs: relationIdentityRhs(),
  })
}

function truthMaterial(): DiagramWithBoundary {
  return finishDiagramWithBoundary(emptyGraph(), [])
}

function truthRhs(): DiagramWithBoundary {
  let graph = emptyGraph()
  const witness = declareWire(graph, graph.root, PROPOSITION)
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

export function truthReification(): Theorem {
  const blank = emptyGraph()
  const lhs = finishDiagramWithBoundary(blank, [])
  const recorder = new PrimitiveStepRecorder(
    lhs.diagram,
    verifyTheory({ relations: [], theorems: [] }),
  )
  return recordExplicitReification({
    name: 'truthReification',
    lhs,
    recorder,
    witnessScope: recorder.diagram.root,
    formalSignatures: [],
    material: truthMaterial(),
    parameters: [],
    rhs: truthRhs(),
  })
}

function drawRightIdentityCarrier(
  initial: GraphConstruction,
  region: RegionId,
  inductionVariable: WireId,
  captures: readonly WireId[],
): GraphConstruction {
  const [zero, plus] = captures
  const quantified = quantifierScope(initial, region, 'forall', [IOTA])
  const zeroValue = quantified.value.variables[0]!
  const claim = implication(quantified.graph, quantified.value.body)
  let graph = claim.graph
  graph = atom(
    graph,
    claim.value.antecedent,
    zero!,
    [zeroValue],
  ).graph
  return atom(
    graph,
    claim.value.consequent,
    plus!,
    [inductionVariable, zeroValue, inductionVariable],
  ).graph
}

function drawAdditionTotality(
  initial: GraphConstruction,
  region: RegionId,
  inductionVariable: WireId,
  plus: WireId,
): GraphConstruction {
  const quantified = quantifierScope(
    initial,
    region,
    'forall',
    [IOTA],
  )
  const right = quantified.value.variables[0]!
  const output = declareWire(
    quantified.graph,
    quantified.value.body,
    IOTA,
  )
  return atom(
    output.graph,
    quantified.value.body,
    plus,
    [inductionVariable, right, output.value],
  ).graph
}

function drawAssociativityCarrier(
  initial: GraphConstruction,
  region: RegionId,
  inductionVariable: WireId,
  captures: readonly WireId[],
): GraphConstruction {
  const plus = captures[0]!
  let graph = drawAdditionTotality(
    initial,
    region,
    inductionVariable,
    plus,
  )
  const quantified = quantifierScope(
    graph,
    region,
    'forall',
    [IOTA, IOTA, IOTA, IOTA],
  )
  const [right, third, firstSum, innerSum] =
    quantified.value.variables
  const claim = implication(quantified.graph, quantified.value.body)
  graph = claim.graph
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
    [right!, third!, innerSum!],
  ).graph
  const output = declareWire(graph, claim.value.consequent, IOTA)
  graph = output.graph
  graph = atom(
    graph,
    claim.value.consequent,
    plus,
    [firstSum!, third!, output.value],
  ).graph
  return atom(
    graph,
    claim.value.consequent,
    plus,
    [inductionVariable, innerSum!, output.value],
  ).graph
}

function drawSuccessorShiftCarrier(
  initial: GraphConstruction,
  region: RegionId,
  inductionVariable: WireId,
  captures: readonly WireId[],
): GraphConstruction {
  const [successor, plus] = captures
  const withTotality = drawAdditionTotality(
    initial,
    region,
    inductionVariable,
    plus!,
  )
  const quantified = quantifierScope(
    withTotality,
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

function drawCommutativityCarrier(
  initial: GraphConstruction,
  region: RegionId,
  inductionVariable: WireId,
  captures: readonly WireId[],
): GraphConstruction {
  const [plus, right] = captures
  const withTotality = drawAdditionTotality(
    initial,
    region,
    inductionVariable,
    plus!,
  )
  const quantified = quantifierScope(
    withTotality,
    region,
    'forall',
    [IOTA],
  )
  const output = quantified.value.variables[0]!
  const claim = implication(quantified.graph, quantified.value.body)
  let graph = claim.graph
  graph = atom(
    graph,
    claim.value.antecedent,
    plus!,
    [inductionVariable, right!, output],
  ).graph
  return atom(
    graph,
    claim.value.consequent,
    plus!,
    [right!, inductionVariable, output],
  ).graph
}

export function rightIdentityInductionReification(): Theorem {
  return recordedUnaryReification(
    'rightIdentityInductionReification',
    [UNARY, TERNARY],
    drawRightIdentityCarrier,
  )
}

export function associativityInductionReification(): Theorem {
  return recordedUnaryReification(
    'associativityInductionReification',
    [TERNARY],
    drawAssociativityCarrier,
  )
}

export function successorShiftInductionReification(): Theorem {
  return recordedUnaryReification(
    'successorShiftInductionReification',
    [BINARY, TERNARY],
    drawSuccessorShiftCarrier,
  )
}

export function commutativityInductionReification(): Theorem {
  return recordedUnaryReification(
    'commutativityInductionReification',
    [TERNARY, IOTA],
    drawCommutativityCarrier,
  )
}
