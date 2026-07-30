import { readFileSync, readdirSync } from 'node:fs'
import { fileURLToPath } from 'node:url'
import { describe, expect, it } from 'vitest'
import { exploreForm } from '../../src/kernel/diagram/canonical/explore'
import type {
  Diagram,
  RegionId,
} from '../../src/kernel/diagram/diagram'
import { isAncestorOrEqual } from '../../src/kernel/diagram/regions'
import {
  checkOccurrenceCertificate,
} from '../../src/kernel/diagram/subgraph/occurrence-certificate'
import {
  occurrenceToSelection,
} from '../../src/kernel/diagram/subgraph/occurrence'
import type {
  SubgraphSelection,
} from '../../src/kernel/diagram/subgraph/selection'
import {
  selectionContents,
} from '../../src/kernel/diagram/subgraph/selection'
import { extractSubgraph } from '../../src/kernel/diagram/subgraph/extract'
import { removeSubgraph } from '../../src/kernel/diagram/subgraph/splice'
import type { Theorem } from '../../src/kernel/proof/theorem'
import {
  registerTheorem,
  verifyTheory,
  type ProofContext,
  type Theory,
} from '../../src/kernel/proof/context'
import {
  applyAction,
  replayActions,
} from '../../src/kernel/proof/action'
import type {
  ProofStep,
  StepReceipt,
} from '../../src/kernel/proof/step'
import { buildFregeTheory } from '../../src/theories'
import { buildArithmeticBase } from '../../src/theories/arithmetic-base'
import {
  buildArithmeticAssociativityTheorems,
} from '../../src/theories/arithmetic-assoc'
import {
  buildNaturalBaseTheorems,
} from '../../src/theories/arithmetic-naturals'
import { buildOneTheorem } from '../../src/theories/arithmetic-one'
import { buildRightUnitTheorem } from '../../src/theories/arithmetic-right'
import {
  BINARY,
  TERNARY,
  UNARY,
  directCuts,
  directNodes,
  endpointWire,
  exactOne,
  natHereditaryParts,
  nodeWithHead,
  relationWire,
  scopedWires,
} from '../../src/theories/arithmetic-support'
import { buildLogicalTheoremPrefix } from '../../src/theories/logic'
import { natRelation } from '../../src/theories/naturals'
import {
  ARITHMETIC_CONTRACTS,
  buildArithmeticStatements,
  type ArithmeticStatementName,
  type HypothesisName,
} from '../../src/theories/statements'

const BASE_NATURAL_CONTRACTS = {
  plusLeftUnit: {
    primitives: ['zero', 'plus'],
    hypotheses: ['plusBase', 'plusSingleValued'],
  },
  zeroIsNat: {
    primitives: ['zero', 'successor'],
    hypotheses: ['zeroExists'],
  },
  succNat: {
    primitives: ['zero', 'successor'],
    hypotheses: [],
  },
  oneIsNat: {
    primitives: ['zero', 'successor'],
    hypotheses: ['zeroExists', 'successorTotal'],
  },
} as const satisfies Readonly<
  Partial<Record<ArithmeticStatementName, {
    readonly primitives: readonly ('zero' | 'successor' | 'plus')[]
    readonly hypotheses: readonly HypothesisName[]
  }>>
>

const BASE_NATURAL_NAMES = Object.keys(
  BASE_NATURAL_CONTRACTS,
) as readonly (keyof typeof BASE_NATURAL_CONTRACTS)[]

const RIGHT_ASSOC_CONTRACTS = {
  rightIdentityCarrierInductive: {
    primitives: ['zero', 'successor', 'plus'],
    hypotheses: ['zeroUnique', 'plusBase', 'plusStep'],
  },
  plusRightUnit: {
    primitives: ['zero', 'successor', 'plus'],
    hypotheses: ['zeroUnique', 'plusBase', 'plusStep', 'plusSingleValued'],
  },
  associativityCarrierBase: {
    primitives: ['zero', 'plus'],
    hypotheses: ['plusBase', 'plusSingleValued'],
  },
  associativityCarrierHereditary: {
    primitives: ['successor', 'plus'],
    hypotheses: ['successorTotal', 'plusStep', 'plusSingleValued'],
  },
  plusAssoc: {
    primitives: ['zero', 'successor', 'plus'],
    hypotheses: [
      'successorTotal',
      'plusBase',
      'plusStep',
      'plusSingleValued',
    ],
  },
} as const satisfies Readonly<
  Partial<Record<ArithmeticStatementName, {
    readonly primitives: readonly ('zero' | 'successor' | 'plus')[]
    readonly hypotheses: readonly HypothesisName[]
  }>>
>

const RIGHT_ASSOC_NAMES = Object.keys(
  RIGHT_ASSOC_CONTRACTS,
) as readonly (keyof typeof RIGHT_ASSOC_CONTRACTS)[]

const SHIFT_COMM_CONTRACTS = {
  successorShiftCarrierInductive: {
    primitives: ['zero', 'successor', 'plus'],
    hypotheses: [
      'successorTotal',
      'successorSingleValued',
      'plusBase',
      'plusStep',
      'plusSingleValued',
    ],
  },
  succShiftS: {
    primitives: ['zero', 'successor', 'plus'],
    hypotheses: [
      'successorTotal',
      'successorSingleValued',
      'plusBase',
      'plusStep',
      'plusSingleValued',
    ],
  },
  commutativityCarrierInductive: {
    primitives: ['zero', 'successor', 'plus'],
    hypotheses: [
      'zeroUnique',
      'successorTotal',
      'successorSingleValued',
      'plusBase',
      'plusStep',
      'plusSingleValued',
    ],
  },
  plusComm: {
    primitives: ['zero', 'successor', 'plus'],
    hypotheses: [
      'zeroUnique',
      'successorTotal',
      'successorSingleValued',
      'plusBase',
      'plusStep',
      'plusSingleValued',
    ],
  },
} as const satisfies Readonly<
  Partial<Record<ArithmeticStatementName, {
    readonly primitives: readonly ('zero' | 'successor' | 'plus')[]
    readonly hypotheses: readonly HypothesisName[]
  }>>
>

const SHIFT_COMM_NAMES = Object.keys(
  SHIFT_COMM_CONTRACTS,
) as readonly (keyof typeof SHIFT_COMM_CONTRACTS)[]

const HYPOTHESIS_ACTION_TERMS: Readonly<
  Record<HypothesisName, readonly string[]>
> = {
  zeroExists: ['existential-zero hypothesis'],
  zeroUnique: ['zero-uniqueness'],
  successorTotal: ['successor-totality hypothesis'],
  successorSingleValued: ['functional-successor'],
  plusBase: ['addition-base hypothesis'],
  plusStep: ['addition-step hypothesis'],
  plusSingleValued: ['functional-addition'],
}

const REQUIRED_ARITHMETIC_ORDER = [
  'plusLeftUnit',
  'zeroIsNat',
  'succNat',
  'oneIsNat',
  'plusRightUnit',
  'plusAssoc',
  'succShiftS',
  'plusComm',
] as const

const CARRIER_SUPPORT = [
  ['rightIdentityCarrierInductive', 'plusRightUnit'],
  ['associativityCarrierBase', 'plusAssoc'],
  ['associativityCarrierHereditary', 'plusAssoc'],
  ['successorShiftCarrierInductive', 'succShiftS'],
  ['commutativityCarrierInductive', 'plusComm'],
] as const

const LOGICAL_PREFIX_ORDER = [
  'ordinaryEqualityContradiction',
  'relationIdentityReification',
  'truthReification',
  'rightIdentityInductionReification',
  'associativityInductionReification',
  'successorShiftInductionReification',
  'commutativityInductionReification',
  'existsProp',
] as const

function buildBaseNaturalTheory(): Theory {
  const relations: Theory['relations'] = [['nat', natRelation()]]
  const statements = buildArithmeticStatements()
  const logical = buildLogicalTheoremPrefix(relations)
  const base = buildArithmeticBase(relations, logical, statements)
  const naturals = buildNaturalBaseTheorems(
    relations,
    [...logical, ...base],
    statements,
  )
  const one = buildOneTheorem(
    relations,
    [...logical, ...base, ...naturals],
    statements,
  )
  return {
    relations,
    theorems: [...logical, ...base, ...naturals, ...one],
  }
}

function buildThroughAssociativityTheory(): Theory {
  const relations: Theory['relations'] = [['nat', natRelation()]]
  const statements = buildArithmeticStatements()
  const logical = buildLogicalTheoremPrefix(relations)
  const base = buildArithmeticBase(relations, logical, statements)
  const naturals = buildNaturalBaseTheorems(
    relations,
    [...logical, ...base],
    statements,
  )
  const one = buildOneTheorem(
    relations,
    [...logical, ...base, ...naturals],
    statements,
  )
  const right = buildRightUnitTheorem(
    relations,
    [...logical, ...base, ...naturals, ...one],
    statements,
  )
  const associativity = buildArithmeticAssociativityTheorems(
    relations,
    [...logical, ...base, ...naturals, ...one, ...right],
    statements,
  )
  return {
    relations,
    theorems: [
      ...logical,
      ...base,
      ...naturals,
      ...one,
      ...right,
      ...associativity,
    ],
  }
}

type ProofTrace = {
  readonly half: 'forward' | 'backward'
  readonly state: number
  readonly before: Diagram
  readonly after: Diagram
  readonly step: ProofStep
  readonly receipt: StepReceipt
  readonly diagnostic: string
}

function traceProofHalf(
  theorem: Theorem,
  context: ProofContext,
  half: 'forward' | 'backward',
): readonly ProofTrace[] {
  const actions = half === 'forward'
    ? theorem.actions
    : (theorem.backActions ?? [])
  let diagram = half === 'forward'
    ? theorem.lhs.diagram
    : theorem.rhs.diagram
  const traces: ProofTrace[] = []
  for (const action of actions) {
    let stepBefore = diagram
    const after = applyAction(
      diagram,
      action,
      context,
      half,
      (next, stepIndex, stepReceipt) => {
        traces.push({
          half,
          state: traces.length,
          before: stepBefore,
          after: next,
          step: action.steps[stepIndex]!,
          receipt: stepReceipt,
          diagnostic: `${action.label} [${stepIndex}]`,
        })
        stepBefore = next
      },
    )
    diagram = after
  }
  return traces
}

function sameIds(
  left: readonly string[],
  right: readonly string[],
): boolean {
  const sortedLeft = [...left].sort()
  const sortedRight = [...right].sort()
  return sortedLeft.length === sortedRight.length
    && sortedLeft.every((id, index) => id === sortedRight[index])
}

function sameSelection(
  left: SubgraphSelection,
  right: SubgraphSelection,
): boolean {
  return left.region === right.region
    && sameIds(left.regions, right.regions)
    && sameIds(left.nodes, right.nodes)
    && sameIds(left.wires, right.wires)
}

function theoremShell(diagram: Diagram) {
  const primitiveScope = exactOne(
    directCuts(diagram, diagram.root),
    'primitive scope',
  )
  const primitiveBody = exactOne(
    directCuts(diagram, primitiveScope),
    'primitive body',
  )
  const antecedent = exactOne(
    directCuts(diagram, primitiveBody),
    'theorem antecedent',
  )
  const children = directCuts(diagram, antecedent)
  const refBearing = children.filter((region) =>
    directNodes(diagram, region).some((node) =>
      diagram.nodes[node]!.kind === 'ref'))
  const conclusion = exactOne(
    refBearing.length > 0
      ? refBearing
      : children.filter((region) =>
          scopedWires(diagram, region).length === 0),
    'theorem conclusion',
  )
  return {
    primitiveScope,
    antecedent,
    conclusion,
  }
}

function structuralHypothesisRegion(
  theorem: Theorem,
  hypothesis: HypothesisName,
): RegionId {
  const diagram = theorem.rhs.diagram
  const shell = theoremShell(diagram)
  const hypothesisRegions = directCuts(diagram, shell.antecedent)
    .filter((region) => region !== shell.conclusion)
  const quantifiedArity: Readonly<
    Partial<Record<HypothesisName, number>>
  > = {
    zeroUnique: 2,
    successorTotal: 1,
    successorSingleValued: 3,
    plusBase: 2,
    plusStep: 5,
    plusSingleValued: 4,
  }
  const arity = quantifiedArity[hypothesis]
  if (arity === undefined) {
    throw new Error(`unsupported structural hypothesis '${hypothesis}'`)
  }
  const arityMatches = hypothesisRegions.filter((region) =>
    scopedWires(diagram, region).length === arity)
  if (hypothesis !== 'zeroUnique' && hypothesis !== 'plusBase') {
    return exactOne(arityMatches, `${hypothesis} hypothesis`)
  }

  const zero = relationWire(diagram, shell.primitiveScope, UNARY)
  return exactOne(
    arityMatches.filter((region) => {
      const body = exactOne(
        directCuts(diagram, region),
        `${hypothesis} universal body`,
      )
      const antecedent = exactOne(
        directCuts(diagram, body),
        `${hypothesis} antecedent`,
      )
      const zeroPremiseCount = directNodes(diagram, antecedent)
        .filter((node) =>
          diagram.nodes[node]!.kind === 'atom'
          && endpointWire(diagram, node, 'head') === zero)
        .length
      return zeroPremiseCount === (
        hypothesis === 'zeroUnique' ? 2 : 1
      )
    }),
    `${hypothesis} hypothesis`,
  )
}

function universalClaimParts(
  diagram: Diagram,
  conclusion: RegionId,
) {
  const scope = exactOne(
    directCuts(diagram, conclusion),
    'claim universal scope',
  )
  const body = exactOne(
    directCuts(diagram, scope),
    'claim universal body',
  )
  const antecedent = exactOne(
    directCuts(diagram, body),
    'claim antecedent',
  )
  const consequent = exactOne(
    directCuts(diagram, antecedent),
    'claim consequent',
  )
  return { scope, antecedent, consequent }
}

function nodeSelection(
  diagram: Diagram,
  node: string,
): SubgraphSelection {
  return {
    region: diagram.nodes[node]!.region,
    regions: [],
    nodes: [node],
    wires: [],
  }
}

function natSelection(
  diagram: Diagram,
  region: RegionId,
  zero: string,
  successor: string,
  individual: string,
  label: string,
): SubgraphSelection {
  const node = exactOne(
    directNodes(diagram, region).filter((nodeId) => {
      const node = diagram.nodes[nodeId]!
      return node.kind === 'ref'
        && node.defId === 'nat'
        && endpointWire(diagram, nodeId, 'arg', 0) === zero
        && endpointWire(diagram, nodeId, 'arg', 1) === successor
        && endpointWire(diagram, nodeId, 'arg', 2) === individual
    }),
    label,
  )
  return nodeSelection(diagram, node)
}

function assertCertifiedDeiteration(
  trace: ProofTrace,
  expectedJustifier: SubgraphSelection,
): void {
  if (trace.step.rule !== 'deiteration') {
    throw new Error(
      `expected deiteration, found ${trace.step.rule} (${trace.diagnostic})`,
    )
  }
  expect(
    sameSelection(trace.step.justifier, expectedJustifier),
    trace.diagnostic,
  ).toBe(true)
  expect(
    isAncestorOrEqual(
      trace.before,
      trace.step.justifier.region,
      trace.step.sel.region,
    ),
    trace.diagnostic,
  ).toBe(true)
  const { pattern } = extractSubgraph(trace.before, trace.step.sel)
  expect(
    checkOccurrenceCertificate(
      trace.before,
      pattern,
      trace.step.certificate,
    ),
    trace.diagnostic,
  ).toEqual({ ok: true })
  const certifiedJustifier = occurrenceToSelection(
    trace.before,
    pattern,
    trace.step.certificate,
  )
  expect(
    sameSelection(certifiedJustifier, expectedJustifier),
    trace.diagnostic,
  ).toBe(true)
}

function selectionKey(
  half: ProofTrace['half'],
  state: number,
  selection: SubgraphSelection,
): string {
  return JSON.stringify([
    half,
    state,
    selection.region,
    [...selection.regions].sort(),
    [...selection.nodes].sort(),
    [...selection.wires].sort(),
  ])
}

function iterationCopySelection(
  trace: ProofTrace,
): SubgraphSelection | null {
  if (trace.step.rule !== 'iteration') return null
  const target = trace.step.target
  const regions = Object.entries(trace.after.regions)
    .filter(([id, region]) =>
      trace.before.regions[id] === undefined
      && region.kind === 'cut'
      && region.parent === target)
    .map(([id]) => id)
  const nodes = Object.entries(trace.after.nodes)
    .filter(([id, node]) =>
      trace.before.nodes[id] === undefined
      && node.region === target)
    .map(([id]) => id)
  const wires = Object.entries(trace.after.wires)
    .filter(([id, wire]) =>
      trace.before.wires[id] === undefined
      && wire.scope === target
      && wire.endpoints.length === 0)
    .map(([id]) => id)
  return {
    region: target,
    regions,
    nodes,
    wires,
  }
}

type ProvenanceBranch = {
  readonly half: ProofTrace['half']
  state: number
  readonly regions: Set<string>
  readonly nodes: Set<string>
  readonly wires: Set<string>
  copied: boolean
  specialized: boolean
  certified: boolean
  used: boolean
  unfolded: boolean
}

function provenanceBranch(
  diagram: Diagram,
  selection: SubgraphSelection,
  half: ProofTrace['half'],
  state: number,
): ProvenanceBranch {
  const contents = selectionContents(diagram, selection)
  return {
    half,
    state,
    regions: new Set(contents.allRegions),
    nodes: new Set(contents.allNodes),
    wires: new Set([
      ...contents.internalWires,
      ...contents.touchingWires,
    ]),
    copied: false,
    specialized: false,
    certified: false,
    used: false,
    unfolded: false,
  }
}

function cloneBranch(branch: ProvenanceBranch): ProvenanceBranch {
  return {
    half: branch.half,
    state: branch.state,
    regions: new Set(branch.regions),
    nodes: new Set(branch.nodes),
    wires: new Set(branch.wires),
    copied: branch.copied,
    specialized: branch.specialized,
    certified: branch.certified,
    used: branch.used,
    unfolded: branch.unfolded,
  }
}

function branchOverlapsSelection(
  branch: ProvenanceBranch,
  diagram: Diagram,
  selection: SubgraphSelection,
): boolean {
  const contents = selectionContents(diagram, selection)
  if ([...contents.allRegions].some((id) => branch.regions.has(id))) {
    return true
  }
  if ([...contents.allNodes].some((id) => branch.nodes.has(id))) {
    return true
  }
  if (contents.allRegions.size > 0 || contents.allNodes.size > 0) {
    return false
  }
  return [
    ...contents.internalWires,
    ...contents.touchingWires,
  ].some((id) => branch.wires.has(id))
}

function carryBranch(
  branch: ProvenanceBranch,
  trace: ProofTrace,
): ProvenanceBranch {
  const carried = cloneBranch(branch)
  carried.regions.clear()
  carried.nodes.clear()
  carried.wires.clear()
  for (const id of branch.regions) {
    if (trace.after.regions[id] !== undefined) carried.regions.add(id)
  }
  for (const id of branch.nodes) {
    if (trace.after.nodes[id] !== undefined) carried.nodes.add(id)
  }
  for (const id of branch.wires) {
    const image = trace.receipt.interface.image(id)
    if (image !== undefined && trace.after.wires[image] !== undefined) {
      carried.wires.add(image)
    }
  }
  carried.state = trace.state + 1
  return carried
}

function branchSurvives(branch: ProvenanceBranch, diagram: Diagram): boolean {
  return [...branch.regions].some((id) => diagram.regions[id] !== undefined)
    || [...branch.nodes].some((id) => diagram.nodes[id] !== undefined)
}

function wireJoinTouches(
  branch: ProvenanceBranch,
  step: Extract<ProofStep, { readonly rule: 'wireJoin' }>,
): boolean {
  return branch.wires.has(step.input.a) || branch.wires.has(step.input.b)
}

function assertStructuralProvenanceChain(
  traces: readonly ProofTrace[],
  source: SubgraphSelection,
  premise: string,
  forwardMeeting?: Diagram,
): void {
  if (
    traces.length === 0
    || traces[0]!.half !== 'backward'
    || traces[0]!.state !== 0
    || traces.some(({ half }) => half !== 'backward')
  ) {
    throw new Error(`${premise} provenance must begin at backward state 0`)
  }
  let branches = [
    provenanceBranch(traces[0]!.before, source, 'backward', 0),
  ]

  for (const trace of traces) {
    const next: ProvenanceBranch[] = []
    for (const branch of branches) {
      if (branch.half !== trace.half || branch.state !== trace.state) {
        throw new Error(
          `${premise} provenance branch crossed a proof-half/state boundary`,
        )
      }
      const selected = (
        trace.step.rule === 'iteration'
        || trace.step.rule === 'deiteration'
      )
        ? branchOverlapsSelection(branch, trace.before, trace.step.sel)
        : false
      const justifies = trace.step.rule === 'deiteration'
        && branchOverlapsSelection(
          branch,
          trace.before,
          trace.step.justifier,
        )
      const unfolds = trace.step.rule === 'unfold'
        && branch.nodes.has(trace.step.nodeId)

      const carried = carryBranch(branch, trace)
      if (
        trace.step.rule === 'wireJoin'
        && wireJoinTouches(branch, trace.step)
      ) {
        carried.specialized = true
      }
      if (trace.step.rule === 'deiteration' && (selected || justifies)) {
        assertCertifiedDeiteration(trace, trace.step.justifier)
        carried.certified = true
        if (justifies) carried.used = true
      }
      if (unfolds) {
        carried.unfolded = true
        carried.specialized = true
        for (const id of Object.keys(trace.after.regions)) {
          if (trace.before.regions[id] === undefined) carried.regions.add(id)
        }
        for (const id of Object.keys(trace.after.nodes)) {
          if (trace.before.nodes[id] === undefined) carried.nodes.add(id)
        }
        for (const id of Object.keys(trace.after.wires)) {
          if (trace.before.wires[id] === undefined) carried.wires.add(id)
        }
      }
      next.push(carried)

      if (trace.step.rule === 'iteration' && selected) {
        const copy = iterationCopySelection(trace)
        if (copy !== null) {
          const copied = provenanceBranch(
            trace.after,
            copy,
            trace.half,
            trace.state + 1,
          )
          copied.copied = true
          next.push(copied)
        }
      }
    }
    branches = next
  }

  const backwardMeeting = traces.at(-1)!.after
  if (
    forwardMeeting !== undefined
    && exploreForm(backwardMeeting) !== exploreForm(forwardMeeting)
  ) {
    throw new Error(`${premise} proof halves do not share a meeting state`)
  }
  const successful = branches.some((branch) =>
    branch.used
    || (
      (branch.copied || branch.unfolded)
      && branch.specialized
      && branch.certified
    )
    || (
      (branch.copied || branch.unfolded)
      && branch.specialized
      && forwardMeeting !== undefined
      && branchSurvives(branch, backwardMeeting)
    ))
  expect(
    successful,
    `${premise} transitive structural provenance ${
      JSON.stringify(branches.map((branch) => ({
        copied: branch.copied,
        specialized: branch.specialized,
        certified: branch.certified,
        used: branch.used,
        unfolded: branch.unfolded,
        survivingRegions: branch.regions.size,
        survivingNodes: branch.nodes.size,
      })))
    }`,
  ).toBe(true)
}

describe('relational Frege arithmetic proofs', () => {
  it('declares the exact base and natural-number proof contracts', () => {
    for (const name of BASE_NATURAL_NAMES) {
      expect(ARITHMETIC_CONTRACTS[name]).toEqual(
        BASE_NATURAL_CONTRACTS[name],
      )
    }
  })

  it('declares the exact right-unit and associativity proof contracts', () => {
    for (const name of RIGHT_ASSOC_NAMES) {
      expect(ARITHMETIC_CONTRACTS[name]).toEqual(
        RIGHT_ASSOC_CONTRACTS[name],
      )
    }
  })

  it('declares the exact successor-shift and commutativity contracts without zero existence', () => {
    for (const name of SHIFT_COMM_NAMES) {
      expect(ARITHMETIC_CONTRACTS[name]).toEqual(
        SHIFT_COMM_CONTRACTS[name],
      )
      expect(ARITHMETIC_CONTRACTS[name].hypotheses).not.toContain(
        'zeroExists',
      )
    }
  })

  it('does not encode a fixed conclusion-plus-six statement shape', () => {
    const modules = [
      'arithmetic-base.ts',
      'arithmetic-naturals.ts',
      'arithmetic-one.ts',
      'arithmetic-support.ts',
    ]
    const directory = fileURLToPath(
      new URL('../../src/theories', import.meta.url),
    )
    const source = modules
      .map((name) => readFileSync(`${directory}/${name}`, 'utf8'))
      .join('\n')

    expect(source).not.toContain('conclusion plus six')
  })

  it('does not preserve the displaced Task 3 hypothesis bundle parser', () => {
    const modules = [
      'arithmetic-right-carrier.ts',
      'arithmetic-right.ts',
      'arithmetic-assoc-base.ts',
      'arithmetic-assoc-carrier.ts',
      'arithmetic-assoc.ts',
    ]
    const directory = fileURLToPath(
      new URL('../../src/theories', import.meta.url),
    )
    const source = modules
      .map((name) => readFileSync(`${directory}/${name}`, 'utf8'))
      .join('\n')

    expect(source).not.toContain('standingHypothesesContent')
    expect(source).not.toContain('missing carrier-support primitive structure')
  })

  it('classifies Nat hereditary children independently of region storage order', () => {
    const theory = buildBaseNaturalTheory()
    const theoremIndex = theory.theorems.findIndex(
      ({ name }) => name === 'succNat',
    )
    const theorem = theory.theorems[theoremIndex]!
    const context = verifyTheory({
      relations: theory.relations,
      theorems: theory.theorems.slice(0, theoremIndex),
    })
    const meeting = replayActions(
      theorem.lhs.diagram,
      theorem.actions,
      context,
    )
    const hereditaryCandidates = Object.keys(meeting.regions).filter(
      (region) => {
        const counts = directCuts(meeting, region)
          .map((child) => scopedWires(meeting, child).length)
          .sort()
        return counts.join(',') === '0,1,2'
      },
    )
    expect(hereditaryCandidates).toHaveLength(1)
    const hereditary = hereditaryCandidates[0]!
    const children = directCuts(meeting, hereditary)
    const childSet = new Set(children)
    const rotatedChildren = [children[1]!, children[2]!, children[0]!]
    const regionEntries = Object.entries(meeting.regions)
    const firstChildIndex = regionEntries.findIndex(([id]) =>
      childSet.has(id))
    const reorderedEntries = [
      ...regionEntries.slice(0, firstChildIndex),
      ...rotatedChildren.map((id) =>
        [id, meeting.regions[id]!] as const),
      ...regionEntries.slice(firstChildIndex).filter(([id]) =>
        !childSet.has(id)),
    ]
    const reordered = {
      ...meeting,
      regions: Object.fromEntries(reorderedEntries),
    }

    const parts = natHereditaryParts(reordered, hereditary)
    expect(scopedWires(reordered, parts.inherited).length).toBe(0)
    expect(scopedWires(reordered, parts.baseCondition).length).toBe(1)
    expect(scopedWires(reordered, parts.closureCondition).length).toBe(2)
  })

  it('has no obsolete induction-statement or ref-spawn proof path', () => {
    const directory = fileURLToPath(
      new URL('../../src/theories', import.meta.url),
    )
    const source = readdirSync(directory)
      .filter((name) => name.endsWith('.ts'))
      .map((name) => readFileSync(`${directory}/${name}`, 'utf8'))
      .join('\n')

    for (const prohibited of ['induction-statements', 'refSpawn']) {
      expect(source).not.toContain(prohibited)
    }
  })

  it('records and verifies the required arithmetic ordered subsequence', () => {
    const theory = buildFregeTheory()
    const names = theory.theorems.map((theorem) => theorem.name)

    expect(names.slice(0, LOGICAL_PREFIX_ORDER.length)).toEqual(
      LOGICAL_PREFIX_ORDER,
    )
    let precedingIndex = LOGICAL_PREFIX_ORDER.length - 1
    for (const name of REQUIRED_ARITHMETIC_ORDER) {
      const index = names.indexOf(name)
      expect(index, `theorem '${name}'`).toBeGreaterThan(precedingIndex)
      precedingIndex = index
    }
    expect(() => verifyTheory(theory)).not.toThrow()
  })

  it('proves each required exact closed arithmetic statement', () => {
    const theory = buildFregeTheory()
    const statements = buildArithmeticStatements()

    for (const name of REQUIRED_ARITHMETIC_ORDER) {
      const theorem = theory.theorems.find(
        (candidate) => candidate.name === name,
      )
      expect(theorem, `theorem '${name}'`).toBeDefined()
      expect(theorem!.name).toBe(name)
      expect(theorem!.lhs.boundary).toEqual([])
      expect(theorem!.rhs.boundary).toEqual([])
      expect(Object.keys(theorem!.lhs.diagram.regions)).toEqual([
        theorem!.lhs.diagram.root,
      ])
      expect(Object.keys(theorem!.lhs.diagram.nodes)).toEqual([])
      expect(Object.keys(theorem!.lhs.diagram.wires)).toEqual([])
      expect(exploreForm(theorem!.rhs.diagram))
        .toBe(exploreForm(statements[name].diagram))

      const actions = [
        ...theorem!.actions,
        ...(theorem!.backActions ?? []),
      ]
      expect(actions.length).toBeGreaterThan(0)
      expect(actions.every((action) => action.steps.length >= 1)).toBe(true)
    }
  })

  it('uses only selected arithmetic hypotheses in the base and natural prefix', () => {
    const theory = buildBaseNaturalTheory()

    for (const name of BASE_NATURAL_NAMES) {
      const theorem = theory.theorems.find(
        (candidate) => candidate.name === name,
      )!
      const labels = [
        ...theorem.actions,
        ...(theorem.backActions ?? []),
      ].map((action) => action.label)
      const selected = new Set(BASE_NATURAL_CONTRACTS[name].hypotheses)

      for (const [hypothesis, terms] of Object.entries(
        HYPOTHESIS_ACTION_TERMS,
      ) as [HypothesisName, readonly string[]][]) {
        if (selected.has(hypothesis as never)) continue
        for (const term of terms) {
          expect(
            labels.some((label) => label.includes(term)),
            `${name} must not specialize ${hypothesis}`,
          ).toBe(false)
        }
      }
    }
  })

  it('makes every selected base and natural-number premise causal in its proof', () => {
    const original = buildBaseNaturalTheory()
    const theory = {
      ...original,
      theorems: original.theorems.map((theorem) => ({
        ...theorem,
        actions: theorem.actions.map((action, index) => ({
          ...action,
          label: `forward diagnostic ${index}`,
        })),
        ...(theorem.backActions === undefined
          ? {}
          : {
              backActions: theorem.backActions.map((action, index) => ({
                ...action,
                label: `backward diagnostic ${index}`,
              })),
            }),
      })),
    }
    const theoremContext = (name: string) => {
      const theoremIndex = theory.theorems.findIndex(
        (theorem) => theorem.name === name,
      )
      const theorem = theory.theorems[theoremIndex]!
      return {
        theorem,
        context: verifyTheory({
          relations: theory.relations,
          theorems: theory.theorems.slice(0, theoremIndex),
        }),
      }
    }

    const assertIteration = (
      traces: readonly ProofTrace[],
      source: SubgraphSelection,
      target: RegionId,
      premise: string,
    ) => {
      const trace = exactOne(
        traces.filter(({ step }) =>
          step.rule === 'iteration'
          && sameSelection(step.sel, source)),
        `iteration of ${premise}`,
      )
      if (trace.step.rule !== 'iteration') {
        throw new Error(`expected iteration of ${premise}`)
      }
      expect(trace.step.target, trace.diagnostic).toBe(target)
      expect(
        isAncestorOrEqual(
          trace.before,
          trace.step.sel.region,
          trace.step.target,
        ),
        trace.diagnostic,
      ).toBe(true)
    }

    const plus = theoremContext('plusLeftUnit')
    const plusDiagram = plus.theorem.rhs.diagram
    const plusShell = theoremShell(plusDiagram)
    const plusChildren = directCuts(plusDiagram, plusShell.antecedent)
    const plusBase = exactOne(
      plusChildren.filter((region) =>
        scopedWires(plusDiagram, region).length === 2),
      'plusBase hypothesis',
    )
    const plusSingleValued = exactOne(
      plusChildren.filter((region) =>
        scopedWires(plusDiagram, region).length === 4),
      'plusSingleValued hypothesis',
    )
    const plusClaim = universalClaimParts(
      plusDiagram,
      plusShell.conclusion,
    )
    const plusTraces = traceProofHalf(
      plus.theorem,
      plus.context,
      'backward',
    )
    assertIteration(
      plusTraces,
      {
        region: plusShell.antecedent,
        regions: [plusBase],
        nodes: [],
        wires: [],
      },
      plusClaim.antecedent,
      'plusBase',
    )
    assertIteration(
      plusTraces,
      {
        region: plusShell.antecedent,
        regions: [plusSingleValued],
        nodes: [],
        wires: [],
      },
      plusClaim.antecedent,
      'plusSingleValued',
    )

    for (const theoremName of ['zeroIsNat', 'oneIsNat']) {
      const zeroDependency = theoremContext(theoremName)
      const diagram = zeroDependency.theorem.rhs.diagram
      const shell = theoremShell(diagram)
      const zero = relationWire(diagram, shell.primitiveScope, UNARY)
      const zeroOccurrence = nodeSelection(
        diagram,
        nodeWithHead(diagram, shell.antecedent, zero),
      )
      const traces = traceProofHalf(
        zeroDependency.theorem,
        zeroDependency.context,
        'backward',
      )
      const deiteration = exactOne(
        traces.filter(({ step }) =>
          step.rule === 'deiteration'
          && sameSelection(step.justifier, zeroOccurrence)),
        `${theoremName} zeroExists deiteration`,
      )
      assertCertifiedDeiteration(deiteration, zeroOccurrence)
    }

    const one = theoremContext('oneIsNat')
    const oneDiagram = one.theorem.rhs.diagram
    const oneShell = theoremShell(oneDiagram)
    const successor = relationWire(
      oneDiagram,
      oneShell.primitiveScope,
      BINARY,
    )
    const successorTotal = exactOne(
      directCuts(oneDiagram, oneShell.antecedent).filter((region) => {
        if (scopedWires(oneDiagram, region).length !== 1) return false
        const body = exactOne(
          directCuts(oneDiagram, region),
          'successorTotal body',
        )
        return directNodes(oneDiagram, body).some((node) =>
          endpointWire(oneDiagram, node, 'head') === successor)
      }),
      'successorTotal hypothesis',
    )
    assertIteration(
      traceProofHalf(one.theorem, one.context, 'backward'),
      {
        region: oneShell.antecedent,
        regions: [successorTotal],
        nodes: [],
        wires: [],
      },
      oneShell.antecedent,
      'successorTotal',
    )

    const succ = theoremContext('succNat')
    const succDiagram = succ.theorem.rhs.diagram
    const succShell = theoremShell(succDiagram)
    const succClaim = universalClaimParts(
      succDiagram,
      succShell.conclusion,
    )
    const succRelation = relationWire(
      succDiagram,
      succShell.primitiveScope,
      BINARY,
    )
    const statementNat = exactOne(
      directNodes(succDiagram, succClaim.antecedent).filter((node) => {
        const value = succDiagram.nodes[node]!
        return value.kind === 'ref' && value.defId === 'nat'
      }),
      'explicit Nat(n) statement premise',
    )
    const statementSuccessor = nodeWithHead(
      succDiagram,
      succClaim.antecedent,
      succRelation,
    )
    const statementZeroRelation = relationWire(
      succDiagram,
      succShell.primitiveScope,
      UNARY,
    )
    expect(endpointWire(succDiagram, statementNat, 'arg', 0))
      .toBe(statementZeroRelation)
    expect(endpointWire(succDiagram, statementNat, 'arg', 1))
      .toBe(succRelation)
    const statementPredecessor = endpointWire(
      succDiagram,
      statementNat,
      'arg',
      2,
    )
    expect(endpointWire(succDiagram, statementSuccessor, 'arg', 0))
      .toBe(statementPredecessor)
    expect(succDiagram.wires[statementPredecessor]!.scope)
      .toBe(succClaim.scope)
    expect(
      succDiagram.wires[
        endpointWire(succDiagram, statementSuccessor, 'arg', 1)
      ]!.scope,
    ).toBe(succClaim.scope)
    const succTraces = traceProofHalf(
      succ.theorem,
      succ.context,
      'forward',
    )
    const natIteration = exactOne(
      succTraces.filter(({ before, step }) => {
        if (step.rule !== 'iteration' || step.sel.nodes.length !== 1) {
          return false
        }
        const shell = theoremShell(before)
        const claim = universalClaimParts(before, shell.conclusion)
        const nodeId = step.sel.nodes[0]!
        const node = before.nodes[nodeId]
        if (
          node?.kind !== 'ref'
          || node.defId !== 'nat'
          || step.sel.region !== claim.antecedent
        ) return false
        const zero = relationWire(before, shell.primitiveScope, UNARY)
        const successor = relationWire(before, shell.primitiveScope, BINARY)
        const successorPremise = nodeWithHead(
          before,
          claim.antecedent,
          successor,
        )
        return endpointWire(before, nodeId, 'arg', 0) === zero
          && endpointWire(before, nodeId, 'arg', 1) === successor
          && endpointWire(before, nodeId, 'arg', 2)
            === endpointWire(before, successorPremise, 'arg', 0)
      }),
      'iteration of explicit Nat(n) premise',
    )
    if (natIteration.step.rule !== 'iteration') {
      throw new Error('expected Nat(n) iteration')
    }
    const natIterationShell = theoremShell(natIteration.before)
    const natIterationClaim = universalClaimParts(
      natIteration.before,
      natIterationShell.conclusion,
    )
    expect(
      natIteration.step.sel.region,
      natIteration.diagnostic,
    ).toBe(natIterationClaim.antecedent)
    expect(
      natIteration.step.target,
      natIteration.diagnostic,
    ).toBe(natIterationClaim.consequent)
    expect(
      isAncestorOrEqual(
        natIteration.before,
        natIteration.step.sel.region,
        natIteration.step.target,
      ),
      natIteration.diagnostic,
    ).toBe(true)

    const successorDeiteration = exactOne(
      succTraces.filter(({ before, step }) => {
        if (step.rule !== 'deiteration') return false
        const shell = theoremShell(before)
        const claim = universalClaimParts(before, shell.conclusion)
        const relation = relationWire(before, shell.primitiveScope, BINARY)
        const premise = nodeWithHead(before, claim.antecedent, relation)
        const occurrence = nodeSelection(before, premise)
        return sameSelection(step.justifier, occurrence)
      }),
      'deiteration justified by explicit Succ(n,s) premise',
    )
    if (successorDeiteration.step.rule !== 'deiteration') {
      throw new Error('expected Succ(n,s) deiteration')
    }
    const successorShell = theoremShell(successorDeiteration.before)
    const successorClaim = universalClaimParts(
      successorDeiteration.before,
      successorShell.conclusion,
    )
    const replayedSuccessor = relationWire(
      successorDeiteration.before,
      successorShell.primitiveScope,
      BINARY,
    )
    const successorOccurrence = nodeSelection(
      successorDeiteration.before,
      nodeWithHead(
        successorDeiteration.before,
        successorClaim.antecedent,
        replayedSuccessor,
      ),
    )
    assertCertifiedDeiteration(
      successorDeiteration,
      successorOccurrence,
    )
  })

  it('makes every selected right-unit and associativity premise causal', () => {
    const original = buildThroughAssociativityTheory()
    const theory = {
      ...original,
      theorems: original.theorems.map((theorem) => ({
        ...theorem,
        actions: theorem.actions.map((action, index) => ({
          ...action,
          label: `forward diagnostic ${index}`,
        })),
        ...(theorem.backActions === undefined
          ? {}
          : {
              backActions: theorem.backActions.map((action, index) => ({
                ...action,
                label: `backward diagnostic ${index}`,
              })),
            }),
      })),
    }

    for (const name of RIGHT_ASSOC_NAMES) {
      const theoremIndex = theory.theorems.findIndex(
        (candidate) => candidate.name === name,
      )
      const theorem = theory.theorems[theoremIndex]!
      const context = verifyTheory({
        relations: theory.relations,
        theorems: theory.theorems.slice(0, theoremIndex),
      })
      const traces = [
        ...traceProofHalf(theorem, context, 'forward'),
        ...traceProofHalf(theorem, context, 'backward'),
      ]
      for (const hypothesis of RIGHT_ASSOC_CONTRACTS[name].hypotheses) {
        const region = structuralHypothesisRegion(theorem, hypothesis)
        const source = {
          region: theoremShell(theorem.rhs.diagram).antecedent,
          regions: [region],
          nodes: [],
          wires: [],
        } as const
        const provenance = traces.filter(({ step }) =>
          (
            step.rule === 'iteration'
            && sameSelection(step.sel, source)
          )
          || (
            step.rule === 'deiteration'
            && sameSelection(step.justifier, source)
          ))
        expect(
          provenance.length,
          `${name} structural provenance for ${hypothesis}`,
        ).toBeGreaterThan(0)
        for (const trace of provenance) {
          if (trace.step.rule === 'deiteration') {
            assertCertifiedDeiteration(trace, source)
          }
        }
        const weakened = {
          ...theorem,
          rhs: {
            ...theorem.rhs,
            diagram: removeSubgraph(theorem.rhs.diagram, {
              region: source.region,
              regions: [region],
              nodes: [],
              wires: [],
            }),
          },
        }

        expect(
          () => verifyTheory({
            relations: theory.relations,
            theorems: [
              ...theory.theorems.slice(0, theoremIndex),
              weakened,
            ],
          }),
          `${name} without ${hypothesis}`,
        ).toThrow()
      }
    }
  })

  it('makes every exact successor-shift and commutativity premise causally and transitively certified', () => {
    const theory = buildFregeTheory()

    for (const name of SHIFT_COMM_NAMES) {
      const theoremIndex = theory.theorems.findIndex(
        (candidate) => candidate.name === name,
      )
      const theorem = theory.theorems[theoremIndex]!
      const context = verifyTheory({
        relations: theory.relations,
        theorems: theory.theorems.slice(0, theoremIndex),
      })
      const forwardTraces = traceProofHalf(theorem, context, 'forward')
      const backwardTraces = traceProofHalf(theorem, context, 'backward')
      const forwardMeeting = forwardTraces.at(-1)?.after
        ?? theorem.lhs.diagram
      for (const hypothesis of SHIFT_COMM_CONTRACTS[name].hypotheses) {
        const region = structuralHypothesisRegion(theorem, hypothesis)
        const source = {
          region: theoremShell(theorem.rhs.diagram).antecedent,
          regions: [region],
          nodes: [],
          wires: [],
        } as const
        expect(
          selectionKey('forward', 0, source),
          `${name} ${hypothesis} proof-half namespace`,
        ).not.toBe(selectionKey('backward', 0, source))
        expect(
          selectionKey('backward', 0, source),
          `${name} ${hypothesis} state namespace`,
        ).not.toBe(selectionKey('backward', 1, source))
        assertStructuralProvenanceChain(
          backwardTraces,
          source,
          `${name} ${hypothesis}`,
          forwardMeeting,
        )
        if (
          name === 'successorShiftCarrierInductive'
          && hypothesis === 'plusBase'
        ) {
          const copyIndex = backwardTraces.findIndex(({ step }) =>
            step.rule === 'iteration'
            && sameSelection(step.sel, source))
          expect(copyIndex).toBeGreaterThan(-1)
          expect(
            () => assertStructuralProvenanceChain(
              backwardTraces.slice(0, copyIndex + 1),
              source,
              'unused plusBase copy',
            ),
          ).toThrow()
        }
        const weakened = {
          ...theorem,
          rhs: {
            ...theorem.rhs,
            diagram: removeSubgraph(theorem.rhs.diagram, source),
          },
        }
        expect(
          () => verifyTheory({
            relations: theory.relations,
            theorems: [
              ...theory.theorems.slice(0, theoremIndex),
              weakened,
            ],
          }),
          `${name} without ${hypothesis}`,
        ).toThrow()
      }
    }
  })

  it('records closed carrier support theorems before their consumers', () => {
    const theory = buildFregeTheory()
    const statements = buildArithmeticStatements()
    const names = theory.theorems.map(({ name }) => name)

    for (const [supportName, consumerName] of CARRIER_SUPPORT) {
      const supportIndex = names.indexOf(supportName)
      const consumerIndex = names.indexOf(consumerName)
      expect(supportIndex, `support theorem '${supportName}'`).toBeGreaterThan(
        -1,
      )
      expect(consumerIndex).toBeGreaterThan(supportIndex)
      const support = theory.theorems[supportIndex]!
      expect(support.lhs.boundary).toEqual([])
      expect(support.rhs.boundary).toEqual([])
      expect(exploreForm(support.rhs.diagram)).toBe(
        exploreForm(statements[supportName].diagram),
      )
      expect(support.actions.length + (support.backActions?.length ?? 0))
        .toBeGreaterThan(0)
      const citations = [
        ...theory.theorems[consumerIndex]!.actions,
        ...(theory.theorems[consumerIndex]!.backActions ?? []),
      ].flatMap((action) => action.steps)
        .filter((step) => step.rule === 'theorem')
        .map((step) => step.name)
      expect(citations).toContain(supportName)
    }
  })

  it('makes representative carrier support citation indispensable', () => {
    const theory = buildThroughAssociativityTheory()
    expect(() => verifyTheory({
      relations: theory.relations,
      theorems: theory.theorems.filter(
        ({ name }) => name !== 'rightIdentityCarrierInductive',
      ),
    })).toThrow()

    const consumerIndex = theory.theorems.findIndex(
      ({ name }) => name === 'plusRightUnit',
    )
    const consumer = theory.theorems[consumerIndex]!
    const withoutSupportCitation = {
      ...consumer,
      actions: consumer.actions.filter((action) =>
        !action.steps.some((step) =>
          step.rule === 'theorem'
          && step.name === 'rightIdentityCarrierInductive')),
      backActions: (consumer.backActions ?? []).filter((action) =>
        !action.steps.some((step) =>
          step.rule === 'theorem'
          && step.name === 'rightIdentityCarrierInductive')),
    }
    expect(() => verifyTheory({
      relations: theory.relations,
      theorems: [
        ...theory.theorems.slice(0, consumerIndex),
        withoutSupportCitation,
      ],
    })).toThrow()
  })

  it('uses both associativity support citations causally', () => {
    const theory = buildThroughAssociativityTheory()
    const consumerIndex = theory.theorems.findIndex(
      ({ name }) => name === 'plusAssoc',
    )
    const consumer = theory.theorems[consumerIndex]!

    for (const supportName of [
      'associativityCarrierBase',
      'associativityCarrierHereditary',
    ]) {
      const citations = [
        ...consumer.actions,
        ...(consumer.backActions ?? []),
      ].filter((action) => action.steps.some((step) =>
        step.rule === 'theorem' && step.name === supportName))
      expect(citations.length).toBeGreaterThan(0)
      const withoutCitation = {
        ...consumer,
        actions: consumer.actions.filter((action) =>
          !action.steps.some((step) =>
            step.rule === 'theorem' && step.name === supportName)),
        backActions: (consumer.backActions ?? []).filter((action) =>
          !action.steps.some((step) =>
            step.rule === 'theorem' && step.name === supportName)),
      }
      expect(() => verifyTheory({
        relations: theory.relations,
        theorems: [
          ...theory.theorems.slice(0, consumerIndex),
          withoutCitation,
        ],
      })).toThrow()
    }
  })

  it('makes the carrier hereditary arithmetic hypothesis indispensable', () => {
    const theory = buildThroughAssociativityTheory()
    const supportIndex = theory.theorems.findIndex(
      ({ name }) => name === 'rightIdentityCarrierInductive',
    )
    const support = theory.theorems[supportIndex]!
    const primitiveScope = directCuts(
      support.rhs.diagram,
      support.rhs.diagram.root,
    )[0]!
    const primitiveBody = directCuts(
      support.rhs.diagram,
      primitiveScope,
    )[0]!
    const hypotheses = directCuts(
      support.rhs.diagram,
      primitiveBody,
    )[0]!
    const additionStep = directCuts(
      support.rhs.diagram,
      hypotheses,
    ).find((region) =>
      Object.values(support.rhs.diagram.wires)
        .filter((wire) => wire.scope === region).length === 5)
    expect(additionStep).toBeDefined()

    const weakened = {
      ...support,
      rhs: {
        ...support.rhs,
        diagram: removeSubgraph(support.rhs.diagram, {
          region: hypotheses,
          regions: [additionStep!],
          nodes: [],
          wires: [],
        }),
      },
    }
    expect(() => verifyTheory({
      relations: theory.relations,
      theorems: [
        ...theory.theorems.slice(0, supportIndex),
        weakened,
      ],
    })).toThrow()
  })

  it('reuses the supplied right-carrier successor edge in both step positions', () => {
    const theory = buildThroughAssociativityTheory()
    const theoremIndex = theory.theorems.findIndex(
      ({ name }) => name === 'rightIdentityCarrierInductive',
    )
    const theorem = theory.theorems[theoremIndex]!
    const context = verifyTheory({
      relations: theory.relations,
      theorems: theory.theorems.slice(0, theoremIndex),
    })
    const diagram = theorem.rhs.diagram
    const shell = theoremShell(diagram)
    const successor = relationWire(
      diagram,
      shell.primitiveScope,
      BINARY,
    )
    const closure = exactOne(
      directCuts(diagram, shell.conclusion).filter((region) =>
        scopedWires(diagram, region).length === 2),
      'right-carrier closure',
    )
    const closureBody = exactOne(
      directCuts(diagram, closure),
      'right-carrier closure body',
    )
    const closureAntecedent = exactOne(
      directCuts(diagram, closureBody),
      'right-carrier closure antecedent',
    )
    const suppliedSuccessor = nodeSelection(
      diagram,
      nodeWithHead(diagram, closureAntecedent, successor),
    )
    const uses = traceProofHalf(theorem, context, 'backward')
      .filter(({ before, step }) => {
        if (
          step.rule !== 'deiteration'
          || step.sel.nodes.length !== 1
        ) return false
        const [node] = step.sel.nodes
        return before.nodes[node!]?.kind === 'atom'
          && endpointWire(before, node!, 'head')
            === relationWire(
              before,
              theoremShell(before).primitiveScope,
              BINARY,
            )
      })
    expect(uses).toHaveLength(2)
    const direct = exactOne(
      uses.filter(({ step }) =>
        step.rule === 'deiteration'
        && sameSelection(step.justifier, suppliedSuccessor)),
      'direct supplied-successor use',
    )
    if (direct.step.rule !== 'deiteration') {
      throw new Error('expected direct successor deiteration')
    }
    const indirect = exactOne(
      uses.filter((trace) => trace !== direct),
      'transitive supplied-successor use',
    )
    if (indirect.step.rule !== 'deiteration') {
      throw new Error('expected transitive successor deiteration')
    }
    expect(
      sameSelection(indirect.step.justifier, direct.step.sel),
      indirect.diagnostic,
    ).toBe(true)
    assertCertifiedDeiteration(indirect, direct.step.sel)
    assertCertifiedDeiteration(direct, suppliedSuccessor)
  })

  it('replays every arithmetic step against exactly its preceding prefix', () => {
    const theory = buildFregeTheory()
    let context = verifyTheory({
      relations: theory.relations,
      theorems: [],
    })

    for (const [theoremIndex, theorem] of theory.theorems.entries()) {
      const precedingNames = new Set(
        theory.theorems
          .slice(0, theoremIndex)
          .map((preceding) => preceding.name),
      )
      const allActions = [
        ...theorem.actions,
        ...(theorem.backActions ?? []),
      ]
      for (const action of allActions) {
        expect(action.steps.length).toBeGreaterThanOrEqual(1)
        for (const step of action.steps) {
          if (step.rule === 'theorem') {
            expect(precedingNames.has(step.name)).toBe(true)
          }
        }
      }

      const forward = replayActions(
        theorem.lhs.diagram,
        theorem.actions,
        context,
      )
      const backward = replayActions(
        theorem.rhs.diagram,
        theorem.backActions ?? [],
        context,
        undefined,
        'backward',
      )
      expect(exploreForm(forward)).toBe(exploreForm(backward))
      context = registerTheorem(context, theorem)
    }
  })

  it('uses both associativity Nat premises causally', () => {
    const theory = buildThroughAssociativityTheory()
    const theoremIndex = theory.theorems.findIndex(
      ({ name }) => name === 'plusAssoc',
    )
    const theorem = theory.theorems[theoremIndex]!
    const natPremises = Object.entries(theorem.rhs.diagram.nodes)
      .filter(([, node]) => node.kind === 'ref' && node.defId === 'nat')
    expect(natPremises).toHaveLength(2)
    for (const [nodeId, node] of natPremises) {
      const weakened = {
        ...theorem,
        rhs: {
          ...theorem.rhs,
          diagram: removeSubgraph(theorem.rhs.diagram, {
            region: node.region,
            regions: [],
            nodes: [nodeId],
            wires: [],
          }),
        },
      }
      expect(() => verifyTheory({
        relations: theory.relations,
        theorems: [
          ...theory.theorems.slice(0, theoremIndex),
          weakened,
        ],
      })).toThrow()
    }
  })

  it('uses every commutativity Nat premise through its structural proof path', () => {
    const theory = buildFregeTheory()

    for (const name of [
      'commutativityCarrierInductive',
      'plusComm',
    ] as const) {
      const theoremIndex = theory.theorems.findIndex(
        (candidate) => candidate.name === name,
      )
      const theorem = theory.theorems[theoremIndex]!
      const context = verifyTheory({
        relations: theory.relations,
        theorems: theory.theorems.slice(0, theoremIndex),
      })
      const diagram = theorem.rhs.diagram
      const shell = theoremShell(diagram)
      const claim = universalClaimParts(diagram, shell.conclusion)
      const zero = relationWire(diagram, shell.primitiveScope, UNARY)
      const successor = relationWire(
        diagram,
        shell.primitiveScope,
        BINARY,
      )
      const sources = name === 'commutativityCarrierInductive'
        ? [
            natSelection(
              diagram,
              claim.antecedent,
              zero,
              successor,
              exactOne(
                scopedWires(diagram, claim.scope),
                'commutativity-support fixed right',
              ),
              'commutativity-support Nat(b)',
            ),
          ]
        : (() => {
            const plus = relationWire(
              diagram,
              shell.primitiveScope,
              TERNARY,
            )
            const publicPlus = exactOne(
              directNodes(diagram, claim.antecedent).filter((node) =>
                diagram.nodes[node]!.kind === 'atom'
                && endpointWire(diagram, node, 'head') === plus),
              'public Plus(a,b,o)',
            )
            const left = endpointWire(diagram, publicPlus, 'arg', 0)
            const right = endpointWire(diagram, publicPlus, 'arg', 1)
            return [
              natSelection(
                diagram,
                claim.antecedent,
                zero,
                successor,
                left,
                'public Nat(a)',
              ),
              natSelection(
                diagram,
                claim.antecedent,
                zero,
                successor,
                right,
                'public Nat(b)',
              ),
            ]
          })()
      const forwardTraces = traceProofHalf(theorem, context, 'forward')
      const backwardTraces = traceProofHalf(theorem, context, 'backward')
      const forwardMeeting = forwardTraces.at(-1)?.after
        ?? theorem.lhs.diagram

      for (const [index, source] of sources.entries()) {
        assertStructuralProvenanceChain(
          backwardTraces,
          source,
          `${name} Nat premise ${index}`,
          forwardMeeting,
        )
      }
    }
  })
})
