import { describe, expect, it } from 'vitest'
import type { DiagramWithBoundary } from '../../src/kernel/diagram/boundary'
import type {
  Diagram,
  NodeId,
  RegionId,
  WireId,
} from '../../src/kernel/diagram/diagram'
import { IOTA, relSig, sigKey } from '../../src/kernel/diagram/sig'
import { natRelation } from '../../src/theories'
import {
  buildArithmeticStatements,
  type ArithmeticStatementName,
  type HypothesisName,
  type PrimitiveName,
} from '../../src/theories/statements'
import { derivedScope } from '../../src/kernel/diagram/regions'
import { serializeTerm } from '../../src/kernel/term/serialize'

const UNARY = relSig([IOTA])
const BINARY = relSig([IOTA, IOTA])
const TERNARY = relSig([IOTA, IOTA, IOTA])

function exactlyOne<T>(values: readonly T[], what: string): T {
  expect(values, what).toHaveLength(1)
  return values[0]!
}

function directCuts(
  diagram: Diagram,
  parent: RegionId,
): readonly RegionId[] {
  return Object.entries(diagram.regions)
    .filter(([, region]) =>
      region.kind === 'cut' && region.parent === parent)
    .map(([id]) => id)
}

function directNodes(
  diagram: Diagram,
  region: RegionId,
): readonly NodeId[] {
  // Pins hold a wire's quantifier; they are not content, and where they sit
  // is asserted through scopedWires instead.
  return Object.entries(diagram.nodes)
    .filter(([, node]) =>
      node.region === region
      && !(node.kind === 'identity' && node.arity === 1))
    .map(([id]) => id)
}

function scopedWires(
  diagram: Diagram,
  region: RegionId,
  boundary: readonly WireId[] = [],
): readonly WireId[] {
  return Object.keys(diagram.wires)
    .filter((id) => derivedScope(diagram, id, boundary) === region)
}

function endpointWire(
  diagram: Diagram,
  node: NodeId,
  kind: 'head' | 'arg' | 'identity',
  index?: number,
): WireId {
  return exactlyOne(
    Object.entries(diagram.wires)
      .filter(([, wire]) => wire.endpoints.some((endpoint) =>
        endpoint.node === node
        && endpoint.port.kind === kind
        && (
          kind === 'head'
          || (
            endpoint.port.kind !== 'head'
            && endpoint.port.index === index
          )
        )))
      .map(([id]) => id),
    `one ${kind}${index === undefined ? '' : ` ${index}`} wire for '${node}'`,
  )
}

function descriptor(
  diagram: Diagram,
  nodeId: NodeId,
  labels: ReadonlyMap<WireId, string>,
): string {
  const label = (wire: WireId): string => {
    const value = labels.get(wire)
    if (value === undefined) {
      throw new Error(`missing structural label for wire '${wire}'`)
    }
    return value
  }
  const node = diagram.nodes[nodeId]!
  if (node.kind === 'atom') {
    const head = label(endpointWire(diagram, nodeId, 'head'))
    const args = node.sig.args.map((_, index) =>
      label(endpointWire(diagram, nodeId, 'arg', index)))
    return `${head}(${args.join(',')})`
  }
  if (node.kind === 'ref') {
    const args = node.sig.args.map((_, index) =>
      label(endpointWire(diagram, nodeId, 'arg', index)))
    return `${node.defId}(${args.join(',')})`
  }
  if (node.kind === 'term') return serializeTerm(node.term)
  const args = Array.from({ length: node.arity }, (_, index) =>
    label(endpointWire(diagram, nodeId, 'identity', index)))
  return `=(${args.join(',')})`
}

function descriptors(
  diagram: Diagram,
  region: RegionId,
  labels: ReadonlyMap<WireId, string>,
): readonly string[] {
  return directNodes(diagram, region)
    .map((node) => descriptor(diagram, node, labels))
    .sort()
}

type StatementSkeleton = {
  readonly proposition: DiagramWithBoundary
  readonly primitives: ReadonlyMap<PrimitiveName, WireId>
  readonly antecedent: RegionId
  readonly consequent: RegionId
}

type ExpectedContract = {
  readonly primitives: readonly PrimitiveName[]
  readonly hypotheses: readonly HypothesisName[]
}

const EXPECTED_CONTRACTS: Readonly<
  Record<ArithmeticStatementName, ExpectedContract>
> = {
  plusLeftUnit: {
    primitives: ['zero', 'plus'],
    hypotheses: ['plusBase', 'plusSingleValued'],
  },
  zeroIsNat: {
    primitives: ['zero', 'successor'],
    hypotheses: ['zeroExists'],
  },
  succNat: { primitives: ['zero', 'successor'], hypotheses: [] },
  oneIsNat: {
    primitives: ['zero', 'successor'],
    hypotheses: ['zeroExists', 'successorTotal'],
  },
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
    hypotheses: ['successorTotal', 'plusBase', 'plusStep', 'plusSingleValued'],
  },
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
}

const PRIMITIVE_SIGNATURES: Readonly<Record<PrimitiveName, typeof UNARY>> = {
  zero: UNARY,
  successor: BINARY,
  plus: TERNARY,
}

type QuantifiedHypothesisExpectation = {
  readonly variables: number
  readonly existentials?: number
  readonly assertions?: readonly string[]
  readonly premises?: readonly string[]
  readonly conclusions?: readonly string[]
}

const HYPOTHESIS_EXPECTATIONS: Readonly<
  Record<Exclude<HypothesisName, 'zeroExists'>, QuantifiedHypothesisExpectation>
> = {
  zeroUnique: {
    variables: 2,
    premises: ['zero(v0)', 'zero(v1)'],
    conclusions: ['=(v0,v1)'],
  },
  successorTotal: {
    variables: 1,
    existentials: 1,
    assertions: ['succ(v0,e0)'],
  },
  successorSingleValued: {
    variables: 3,
    premises: ['succ(v0,v1)', 'succ(v0,v2)'],
    conclusions: ['=(v1,v2)'],
  },
  plusBase: {
    variables: 2,
    premises: ['zero(v0)'],
    conclusions: ['plus(v0,v1,v1)'],
  },
  plusStep: {
    variables: 5,
    premises: ['plus(v0,v1,v2)', 'succ(v0,v3)', 'succ(v2,v4)'],
    conclusions: ['plus(v3,v1,v4)'],
  },
  plusSingleValued: {
    variables: 4,
    premises: ['plus(v0,v1,v2)', 'plus(v0,v1,v3)'],
    conclusions: ['=(v2,v3)'],
  },
}

function assertStatementContract(
  proposition: DiagramWithBoundary,
  expected: ExpectedContract,
): StatementSkeleton {
  const { diagram } = proposition
  expect(proposition.boundary).toEqual([])
  expect(directNodes(diagram, diagram.root)).toEqual([])
  expect(scopedWires(diagram, diagram.root)).toEqual([])

  const primitiveScope = exactlyOne(
    directCuts(diagram, diagram.root),
    'one outer primitive-relation universal scope',
  )
  const primitives = scopedWires(diagram, primitiveScope)
  expect(primitives.map((wire) => diagram.wires[wire]!.sig))
    .toEqual(expected.primitives.map((name) => PRIMITIVE_SIGNATURES[name]))
  const primitiveEnvironment = new Map<PrimitiveName, WireId>()
  expected.primitives.forEach((name, index) =>
    primitiveEnvironment.set(name, primitives[index]!))

  const universalBody = exactlyOne(
    directCuts(diagram, primitiveScope),
    'one positive primitive-relation body',
  )
  expect(scopedWires(diagram, universalBody)).toEqual([])
  expect(directNodes(diagram, universalBody)).toEqual([])
  const antecedent = exactlyOne(
    directCuts(diagram, universalBody),
    'one theorem antecedent',
  )
  const antecedentCuts = directCuts(diagram, antecedent)
  expect(antecedentCuts, 'the consequent plus selected quantified hypotheses')
    .toHaveLength(expected.hypotheses.filter((name) => name !== 'zeroExists').length + 1)
  const consequent = antecedentCuts[0]!
  expect(directCuts(diagram, consequent)).not.toContain(antecedent)

  const labels = new Map<WireId, string>()
  primitiveEnvironment.forEach((wire, name) => labels.set(wire, name === 'successor' ? 'succ' : name))
  const hasZeroExists = expected.hypotheses.includes('zeroExists')
  const directAntecedentNodes = directNodes(diagram, antecedent)
  expect(directAntecedentNodes).toHaveLength(hasZeroExists ? 1 : 0)
  expect(scopedWires(diagram, antecedent)).toHaveLength(hasZeroExists ? 1 : 0)
  if (hasZeroExists) {
    const existenceAtom = directAntecedentNodes[0]!
    const zero = primitiveEnvironment.get('zero')
    expect(zero, 'zeroExists requires zero').toBeDefined()
    expect(diagram.nodes[existenceAtom]).toMatchObject({
      kind: 'atom',
      region: antecedent,
      sig: UNARY,
    })
    expect(endpointWire(diagram, existenceAtom, 'head')).toBe(zero)
    const witness = endpointWire(diagram, existenceAtom, 'arg', 0)
    expect(diagram.wires[witness]!.sig).toEqual(IOTA)
    expect(derivedScope(diagram, witness)).toBe(antecedent)
  }

  const hypothesisCuts = antecedentCuts.slice(1)
  const quantifiedHypotheses = expected.hypotheses.filter((name) => name !== 'zeroExists')
  expect(hypothesisCuts).toHaveLength(quantifiedHypotheses.length)
  hypothesisCuts.forEach((outer, index) => {
    const name = quantifiedHypotheses[index]!
    assertQuantifiedHypothesis(
      diagram,
      outer,
      labels,
      HYPOTHESIS_EXPECTATIONS[name],
    )
  })

  const refs = Object.values(diagram.nodes)
    .filter((node) => node.kind === 'ref')
  expect(refs.every((node) => node.defId === 'nat')).toBe(true)

  return {
    proposition,
    primitives: primitiveEnvironment,
    antecedent,
    consequent,
  }
}

function assertQuantifiedHypothesis(
  diagram: Diagram,
  outer: RegionId,
  primitiveLabels: ReadonlyMap<WireId, string>,
  expected: QuantifiedHypothesisExpectation,
  boundary: readonly WireId[] = [],
): void {
  const variables = scopedWires(diagram, outer, boundary)
  expect(variables).toHaveLength(expected.variables)
  expect(variables.map((wire) => diagram.wires[wire]!.sig))
    .toEqual(Array.from({ length: expected.variables }, () => IOTA))
  const labels = new Map(primitiveLabels)
  variables.forEach((wire, index) => labels.set(wire, `v${index}`))

  const body = exactlyOne(
    directCuts(diagram, outer),
    'one positive quantified-hypothesis body',
  )
  const existentials = scopedWires(diagram, body, boundary)
  expect(existentials).toHaveLength(expected.existentials ?? 0)
  expect(existentials.map((wire) => diagram.wires[wire]!.sig))
    .toEqual(Array.from(
      { length: expected.existentials ?? 0 },
      () => IOTA,
    ))
  existentials.forEach((wire, index) => labels.set(wire, `e${index}`))

  if (expected.assertions !== undefined) {
    expect(directCuts(diagram, body)).toEqual([])
    expect(descriptors(diagram, body, labels))
      .toEqual([...expected.assertions].sort())
    return
  }

  expect(directNodes(diagram, body)).toEqual([])
  const premise = exactlyOne(
    directCuts(diagram, body),
    'one quantified-hypothesis implication',
  )
  const conclusion = exactlyOne(
    directCuts(diagram, premise),
    'one quantified-hypothesis implication conclusion',
  )
  expect(scopedWires(diagram, premise, boundary)).toEqual([])
  expect(scopedWires(diagram, conclusion, boundary)).toEqual([])
  expect(descriptors(diagram, premise, labels))
    .toEqual([...(expected.premises ?? [])].sort())
  expect(descriptors(diagram, conclusion, labels))
    .toEqual([...(expected.conclusions ?? [])].sort())
}

type ClaimScope = {
  readonly diagram: Diagram
  readonly premise: RegionId
  readonly conclusion: RegionId
  readonly labels: ReadonlyMap<WireId, string>
}

function assertUniversalClaim(
  skeleton: StatementSkeleton,
  variableNames: readonly string[],
): ClaimScope {
  const { diagram } = skeleton.proposition
  expect(directNodes(diagram, skeleton.consequent)).toEqual([])
  expect(scopedWires(diagram, skeleton.consequent)).toEqual([])
  const outer = exactlyOne(
    directCuts(diagram, skeleton.consequent),
    'one theorem-conclusion universal scope',
  )
  const variables = scopedWires(diagram, outer)
  expect(variables).toHaveLength(variableNames.length)
  expect(variables.map((wire) => diagram.wires[wire]!.sig))
    .toEqual(variableNames.map(() => IOTA))
  const labels = new Map<WireId, string>()
  skeleton.primitives.forEach((wire, name) =>
    labels.set(wire, name === 'successor' ? 'succ' : name))
  variables.forEach((wire, index) =>
    labels.set(wire, variableNames[index]!))
  const body = exactlyOne(
    directCuts(diagram, outer),
    'one positive theorem-conclusion universal body',
  )
  expect(directNodes(diagram, body)).toEqual([])
  const premise = exactlyOne(
    directCuts(diagram, body),
    'one theorem-conclusion implication',
  )
  const conclusion = exactlyOne(
    directCuts(diagram, premise),
    'one theorem-conclusion implication consequent',
  )
  return { diagram, premise, conclusion, labels }
}

function assertClaim(
  claim: ClaimScope,
  premises: readonly string[],
  conclusions: readonly string[],
  existentialNames: readonly string[] = [],
): void {
  const labels = new Map(claim.labels)
  const witnesses = scopedWires(claim.diagram, claim.conclusion)
  expect(witnesses).toHaveLength(existentialNames.length)
  expect(witnesses.map((wire) => claim.diagram.wires[wire]!.sig))
    .toEqual(existentialNames.map(() => IOTA))
  witnesses.forEach((wire, index) =>
    labels.set(wire, existentialNames[index]!))
  expect(descriptors(claim.diagram, claim.premise, labels))
    .toEqual([...premises].sort())
  expect(descriptors(claim.diagram, claim.conclusion, labels))
    .toEqual([...conclusions].sort())
  for (const witness of witnesses) {
    expect(claim.diagram.wires[witness]!.endpoints.every((endpoint) =>
      claim.diagram.nodes[endpoint.node]!.region === claim.conclusion))
      .toBe(true)
  }
}

function assertExistentialConclusion(
  skeleton: StatementSkeleton,
  variableNames: readonly string[],
  assertions: readonly string[],
): void {
  const { diagram } = skeleton.proposition
  expect(directCuts(diagram, skeleton.consequent)).toEqual([])
  const witnesses = scopedWires(diagram, skeleton.consequent)
  expect(witnesses).toHaveLength(variableNames.length)
  expect(witnesses.map((wire) => diagram.wires[wire]!.sig))
    .toEqual(variableNames.map(() => IOTA))
  const labels = new Map<WireId, string>()
  skeleton.primitives.forEach((wire, name) =>
    labels.set(wire, name === 'successor' ? 'succ' : name))
  witnesses.forEach((wire, index) =>
    labels.set(wire, variableNames[index]!))
  expect(descriptors(diagram, skeleton.consequent, labels))
    .toEqual([...assertions].sort())
}

describe('relational Frege natural numbers', () => {
  it('defines Nat only from its zero, successor, and individual parameters', () => {
    const definition = natRelation()
    const { diagram } = definition
    expect(definition.boundary.map((wire) =>
      sigKey(diagram.wires[wire]!.sig)))
      .toEqual(['(i)', '(i,i)', 'i'])
    expect(relSig(definition.boundary.map((wire) =>
      diagram.wires[wire]!.sig)))
      .toEqual(relSig([UNARY, BINARY, IOTA]))
    expect(definition.boundary.every((wire) =>
      derivedScope(diagram, wire, definition.boundary) === diagram.root)).toBe(true)
    expect(Object.values(diagram.nodes).every((node) =>
      node.kind !== 'ref')).toBe(true)

    const [zero, succ, candidate] = definition.boundary
    const propertyScope = exactlyOne(
      directCuts(diagram, diagram.root),
      'one universal property scope',
    )
    const property = exactlyOne(
      scopedWires(diagram, propertyScope, definition.boundary),
      'one quantified hereditary property',
    )
    expect(diagram.wires[property]!.sig).toEqual(UNARY)
    const body = exactlyOne(
      directCuts(diagram, propertyScope),
      'one positive universal-property body',
    )
    const antecedent = exactlyOne(
      directCuts(diagram, body),
      'one hereditary-property antecedent',
    )
    const antecedentCuts = directCuts(diagram, antecedent)
    expect(antecedentCuts, 'the conclusion plus two hereditary conditions')
      .toHaveLength(3)
    const consequent = antecedentCuts[0]!
    const labels = new Map<WireId, string>([
      [zero!, 'zero'],
      [succ!, 'succ'],
      [candidate!, 'n'],
      [property, 'property'],
    ])
    expect(descriptors(diagram, consequent, labels)).toEqual(['property(n)'])
    expect(scopedWires(diagram, consequent, definition.boundary)).toEqual([])

    const conditions = antecedentCuts.slice(1)
    assertQuantifiedHypothesis(diagram, conditions[0]!, labels, {
      variables: 1,
      premises: ['zero(v0)'],
      conclusions: ['property(v0)'],
    }, definition.boundary)
    assertQuantifiedHypothesis(diagram, conditions[1]!, labels, {
      variables: 2,
      premises: ['property(v0)', 'succ(v0,v1)'],
      conclusions: ['property(v1)'],
    }, definition.boundary)
  })
})

describe('closed relational arithmetic statements', () => {
  const historicalNames: readonly ArithmeticStatementName[] = [
    'plusLeftUnit',
    'zeroIsNat',
    'succNat',
    'oneIsNat',
    'plusRightUnit',
    'plusAssoc',
    'succShiftS',
    'plusComm',
  ]
  const supportNames: readonly ArithmeticStatementName[] = [
    'rightIdentityCarrierInductive',
    'associativityCarrierBase',
    'associativityCarrierHereditary',
    'successorShiftCarrierInductive',
    'commutativityCarrierInductive',
  ]
  const requiredNames: readonly ArithmeticStatementName[] = [
    'plusLeftUnit',
    'zeroIsNat',
    'succNat',
    'oneIsNat',
    'rightIdentityCarrierInductive',
    'plusRightUnit',
    'associativityCarrierBase',
    'associativityCarrierHereditary',
    'plusAssoc',
    'successorShiftCarrierInductive',
    'succShiftS',
    'commutativityCarrierInductive',
    'plusComm',
  ]
  const statements = buildArithmeticStatements()

  it('constructs historical and support propositions in one authoritative registry', () => {
    const names = Object.keys(statements) as ArithmeticStatementName[]
    let precedingIndex = -1
    for (const name of requiredNames) {
      const index = names.indexOf(name)
      expect(index, `statement '${name}'`).toBeGreaterThan(precedingIndex)
      precedingIndex = index
    }
    expect(new Set(Object.values(statements)).size).toBe(names.length)
    const primitiveWires = new Set<object>()
    for (const name of names) {
      const skeleton = assertStatementContract(
        statements[name],
        EXPECTED_CONTRACTS[name],
      )
      skeleton.primitives.forEach((wire) =>
        primitiveWires.add(skeleton.proposition.diagram.wires[wire]!))
    }
    expect(primitiveWires.size).toBe(
      requiredNames.reduce(
        (count, name) => count + EXPECTED_CONTRACTS[name].primitives.length,
        0,
      ),
    )
    expect(historicalNames).toHaveLength(8)
    expect(supportNames).toHaveLength(5)
  })

  it('states plusLeftUnit without a Nat guard', () => {
    const skeleton = assertStatementContract(
      statements.plusLeftUnit,
      EXPECTED_CONTRACTS.plusLeftUnit,
    )
    const claim = assertUniversalClaim(skeleton, ['z', 'a', 'o'])
    assertClaim(
      claim,
      ['zero(z)', 'plus(z,a,o)'],
      ['=(o,a)'],
    )
  })

  it('states plusRightUnit with Nat of exactly the first addend', () => {
    const skeleton = assertStatementContract(
      statements.plusRightUnit,
      EXPECTED_CONTRACTS.plusRightUnit,
    )
    const claim = assertUniversalClaim(skeleton, ['z', 'a', 'o'])
    assertClaim(
      claim,
      ['nat(zero,succ,a)', 'zero(z)', 'plus(a,z,o)'],
      ['=(o,a)'],
    )
  })

  it('states associativity with distinct Nat guards and an existential intermediate sum', () => {
    const skeleton = assertStatementContract(
      statements.plusAssoc,
      EXPECTED_CONTRACTS.plusAssoc,
    )
    const claim = assertUniversalClaim(skeleton, ['a', 'b', 'c', 't', 'o'])
    assertClaim(
      claim,
      [
        'nat(zero,succ,a)',
        'nat(zero,succ,b)',
        'plus(a,b,t)',
        'plus(t,c,o)',
      ],
      ['plus(b,c,u)', 'plus(a,u,o)'],
      ['u'],
    )

    const natCandidates = directNodes(claim.diagram, claim.premise)
      .filter((node) => claim.diagram.nodes[node]!.kind === 'ref')
      .map((node) => endpointWire(claim.diagram, node, 'arg', 2))
    expect(natCandidates).toHaveLength(2)
    expect(new Set(natCandidates).size).toBe(2)
    expect(natCandidates.map((wire) => claim.labels.get(wire)).sort())
      .toEqual(['a', 'b'])
  })

  it('states zeroIsNat as a closed existential fact', () => {
    const skeleton = assertStatementContract(
      statements.zeroIsNat,
      EXPECTED_CONTRACTS.zeroIsNat,
    )
    assertExistentialConclusion(
      skeleton,
      ['z'],
      ['zero(z)', 'nat(zero,succ,z)'],
    )
    const { diagram } = skeleton.proposition
    const natRef = exactlyOne(
      Object.entries(diagram.nodes)
        .filter(([, node]) => node.kind === 'ref')
        .map(([id]) => id),
      'one folded Nat reference',
    )
    expect(diagram.nodes[natRef]).toMatchObject({ kind: 'ref', defId: 'nat' })
    const refArguments = [0, 1, 2].map((index) =>
      endpointWire(diagram, natRef, 'arg', index))
    expect(refArguments.map((wire) => diagram.wires[wire]!.sig))
      .toEqual([UNARY, BINARY, IOTA])
    const zeroAtom = exactlyOne(
      directNodes(diagram, skeleton.consequent)
        .filter((node) => diagram.nodes[node]!.kind === 'atom'),
      'one zero assertion in the existential conclusion',
    )
    expect(endpointWire(diagram, zeroAtom, 'head'))
      .toBe(skeleton.primitives.get('zero'))
    expect(refArguments[2]).toBe(endpointWire(diagram, zeroAtom, 'arg', 0))
  })

  it('states successor closure with the predecessor Nat guard', () => {
    const skeleton = assertStatementContract(
      statements.succNat,
      EXPECTED_CONTRACTS.succNat,
    )
    const claim = assertUniversalClaim(skeleton, ['n', 's'])
    assertClaim(
      claim,
      ['nat(zero,succ,n)', 'succ(n,s)'],
      ['nat(zero,succ,s)'],
    )
  })

  it('states oneIsNat as one shared zero-successor witness chain', () => {
    const skeleton = assertStatementContract(
      statements.oneIsNat,
      EXPECTED_CONTRACTS.oneIsNat,
    )
    assertExistentialConclusion(
      skeleton,
      ['z', 's'],
      ['zero(z)', 'succ(z,s)', 'nat(zero,succ,s)'],
    )
  })

  it('states successor shift with a contained predecessor-sum witness', () => {
    const skeleton = assertStatementContract(
      statements.succShiftS,
      EXPECTED_CONTRACTS.succShiftS,
    )
    const claim = assertUniversalClaim(skeleton, ['a', 'b', 'sb', 'o'])
    assertClaim(
      claim,
      [
        'nat(zero,succ,a)',
        'succ(b,sb)',
        'plus(a,sb,o)',
      ],
      ['plus(a,b,p)', 'succ(p,o)'],
      ['p'],
    )
  })

  it('states commutativity with Nat guards on both addends', () => {
    const skeleton = assertStatementContract(
      statements.plusComm,
      EXPECTED_CONTRACTS.plusComm,
    )
    const claim = assertUniversalClaim(skeleton, ['a', 'b', 'o'])
    assertClaim(
      claim,
      [
        'nat(zero,succ,a)',
        'nat(zero,succ,b)',
        'plus(a,b,o)',
      ],
      ['plus(b,a,o)'],
    )
  })
})
