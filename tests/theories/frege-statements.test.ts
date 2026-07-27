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
} from '../../src/theories/statements'

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
  return Object.entries(diagram.nodes)
    .filter(([, node]) => node.region === region)
    .map(([id]) => id)
}

function scopedWires(
  diagram: Diagram,
  region: RegionId,
): readonly WireId[] {
  return Object.entries(diagram.wires)
    .filter(([, wire]) => wire.scope === region)
    .map(([id]) => id)
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
  readonly zero: WireId
  readonly succ: WireId
  readonly plus: WireId
  readonly antecedent: RegionId
  readonly consequent: RegionId
}

function assertStatementSkeleton(
  proposition: DiagramWithBoundary,
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
    .toEqual([UNARY, BINARY, TERNARY])
  expect(primitives.map((wire) => sigKey(diagram.wires[wire]!.sig)))
    .toEqual(['(i)', '(i,i)', '(i,i,i)'])
  const [zero, succ, plus] = primitives

  const universalBody = exactlyOne(
    directCuts(diagram, primitiveScope),
    'one positive primitive-relation body',
  )
  expect(scopedWires(diagram, universalBody)).toEqual([])
  expect(directNodes(diagram, universalBody)).toEqual([])
  const antecedent = exactlyOne(
    directCuts(diagram, universalBody),
    'one standing-hypothesis antecedent',
  )
  const antecedentCuts = directCuts(diagram, antecedent)
  expect(antecedentCuts, 'the consequent plus six quantified hypotheses')
    .toHaveLength(7)
  const consequent = antecedentCuts[0]!
  expect(directCuts(diagram, consequent)).not.toContain(antecedent)

  const refs = Object.values(diagram.nodes)
    .filter((node) => node.kind === 'ref')
  expect(refs.every((node) => node.defId === 'nat')).toBe(true)

  return {
    proposition,
    zero: zero!,
    succ: succ!,
    plus: plus!,
    antecedent,
    consequent,
  }
}

type QuantifiedHypothesisExpectation = {
  readonly variables: number
  readonly existentials?: number
  readonly assertions?: readonly string[]
  readonly premises?: readonly string[]
  readonly conclusions?: readonly string[]
}

function assertQuantifiedHypothesis(
  diagram: Diagram,
  outer: RegionId,
  primitiveLabels: ReadonlyMap<WireId, string>,
  expected: QuantifiedHypothesisExpectation,
): void {
  const variables = scopedWires(diagram, outer)
  expect(variables).toHaveLength(expected.variables)
  expect(variables.map((wire) => diagram.wires[wire]!.sig))
    .toEqual(Array.from({ length: expected.variables }, () => IOTA))
  const labels = new Map(primitiveLabels)
  variables.forEach((wire, index) => labels.set(wire, `v${index}`))

  const body = exactlyOne(
    directCuts(diagram, outer),
    'one positive quantified-hypothesis body',
  )
  const existentials = scopedWires(diagram, body)
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
  expect(scopedWires(diagram, premise)).toEqual([])
  expect(scopedWires(diagram, conclusion)).toEqual([])
  expect(descriptors(diagram, premise, labels))
    .toEqual([...(expected.premises ?? [])].sort())
  expect(descriptors(diagram, conclusion, labels))
    .toEqual([...(expected.conclusions ?? [])].sort())
}

function assertStandingHypotheses(skeleton: StatementSkeleton): void {
  const { diagram } = skeleton.proposition
  const labels = new Map<WireId, string>([
    [skeleton.zero, 'zero'],
    [skeleton.succ, 'succ'],
    [skeleton.plus, 'plus'],
  ])

  const existenceAtom = exactlyOne(
    directNodes(diagram, skeleton.antecedent),
    'the inline existential zero hypothesis',
  )
  const zeroWitness = endpointWire(diagram, existenceAtom, 'arg', 0)
  expect(diagram.nodes[existenceAtom]).toMatchObject({
    kind: 'atom',
    region: skeleton.antecedent,
    sig: UNARY,
  })
  expect(endpointWire(diagram, existenceAtom, 'head')).toBe(skeleton.zero)
  expect(diagram.wires[zeroWitness]).toMatchObject({
    scope: skeleton.antecedent,
    sig: IOTA,
  })
  expect(scopedWires(diagram, skeleton.antecedent)).toEqual([zeroWitness])

  const quantified = directCuts(diagram, skeleton.antecedent)
    .filter((region) => region !== skeleton.consequent)
  expect(quantified).toHaveLength(6)
  const expectations: readonly QuantifiedHypothesisExpectation[] = [
    {
      variables: 2,
      premises: ['zero(v0)', 'zero(v1)'],
      conclusions: ['=(v0,v1)'],
    },
    {
      variables: 1,
      existentials: 1,
      assertions: ['succ(v0,e0)'],
    },
    {
      variables: 3,
      premises: ['succ(v0,v1)', 'succ(v0,v2)'],
      conclusions: ['=(v1,v2)'],
    },
    {
      variables: 2,
      premises: ['zero(v0)'],
      conclusions: ['plus(v0,v1,v1)'],
    },
    {
      variables: 5,
      premises: [
        'plus(v0,v1,v2)',
        'succ(v0,v3)',
        'succ(v2,v4)',
      ],
      conclusions: ['plus(v3,v1,v4)'],
    },
    {
      variables: 4,
      premises: ['plus(v0,v1,v2)', 'plus(v0,v1,v3)'],
      conclusions: ['=(v2,v3)'],
    },
  ]
  quantified.forEach((outer, index) => {
    assertQuantifiedHypothesis(
      diagram,
      outer,
      labels,
      expectations[index]!,
    )
  })
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
  const labels = new Map<WireId, string>([
    [skeleton.zero, 'zero'],
    [skeleton.succ, 'succ'],
    [skeleton.plus, 'plus'],
  ])
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
  const labels = new Map<WireId, string>([
    [skeleton.zero, 'zero'],
    [skeleton.succ, 'succ'],
    [skeleton.plus, 'plus'],
  ])
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
      diagram.wires[wire]!.scope === diagram.root)).toBe(true)
    expect(Object.values(diagram.nodes).every((node) =>
      node.kind !== 'ref')).toBe(true)

    const [zero, succ, candidate] = definition.boundary
    const propertyScope = exactlyOne(
      directCuts(diagram, diagram.root),
      'one universal property scope',
    )
    const property = exactlyOne(
      scopedWires(diagram, propertyScope),
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
    expect(scopedWires(diagram, consequent)).toEqual([])

    const conditions = antecedentCuts.slice(1)
    assertQuantifiedHypothesis(diagram, conditions[0]!, labels, {
      variables: 1,
      premises: ['zero(v0)'],
      conclusions: ['property(v0)'],
    })
    assertQuantifiedHypothesis(diagram, conditions[1]!, labels, {
      variables: 2,
      premises: ['property(v0)', 'succ(v0,v1)'],
      conclusions: ['property(v1)'],
    })
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
      const skeleton = assertStatementSkeleton(statements[name])
      assertStandingHypotheses(skeleton)
      primitiveWires.add(
        skeleton.proposition.diagram.wires[skeleton.zero]!,
      )
      primitiveWires.add(
        skeleton.proposition.diagram.wires[skeleton.succ]!,
      )
      primitiveWires.add(
        skeleton.proposition.diagram.wires[skeleton.plus]!,
      )
    }
    expect(primitiveWires.size).toBe(names.length * 3)
    expect(historicalNames).toHaveLength(8)
    expect(supportNames).toHaveLength(5)
  })

  it('states plusLeftUnit without a Nat guard', () => {
    const skeleton = assertStatementSkeleton(statements.plusLeftUnit)
    const claim = assertUniversalClaim(skeleton, ['z', 'a', 'o'])
    assertClaim(
      claim,
      ['zero(z)', 'plus(z,a,o)'],
      ['=(o,a)'],
    )
  })

  it('states plusRightUnit with Nat of exactly the first addend', () => {
    const skeleton = assertStatementSkeleton(statements.plusRightUnit)
    const claim = assertUniversalClaim(skeleton, ['z', 'a', 'o'])
    assertClaim(
      claim,
      ['nat(zero,succ,a)', 'zero(z)', 'plus(a,z,o)'],
      ['=(o,a)'],
    )
  })

  it('states associativity with distinct Nat guards and an existential intermediate sum', () => {
    const skeleton = assertStatementSkeleton(statements.plusAssoc)
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
    const skeleton = assertStatementSkeleton(statements.zeroIsNat)
    assertExistentialConclusion(
      skeleton,
      ['z'],
      ['zero(z)', 'nat(zero,succ,z)'],
    )
  })

  it('states successor closure with the predecessor Nat guard', () => {
    const skeleton = assertStatementSkeleton(statements.succNat)
    const claim = assertUniversalClaim(skeleton, ['n', 's'])
    assertClaim(
      claim,
      ['nat(zero,succ,n)', 'succ(n,s)'],
      ['nat(zero,succ,s)'],
    )
  })

  it('states oneIsNat as one shared zero-successor witness chain', () => {
    const skeleton = assertStatementSkeleton(statements.oneIsNat)
    assertExistentialConclusion(
      skeleton,
      ['z', 's'],
      ['zero(z)', 'succ(z,s)', 'nat(zero,succ,s)'],
    )
  })

  it('states successor shift with a contained predecessor-sum witness', () => {
    const skeleton = assertStatementSkeleton(statements.succShiftS)
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
    const skeleton = assertStatementSkeleton(statements.plusComm)
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
