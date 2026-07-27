import { readFileSync, readdirSync } from 'node:fs'
import { fileURLToPath } from 'node:url'
import { describe, expect, it } from 'vitest'
import { exploreForm } from '../../src/kernel/diagram/canonical/explore'
import { removeSubgraph } from '../../src/kernel/diagram/subgraph/splice'
import {
  registerTheorem,
  verifyTheory,
} from '../../src/kernel/proof/context'
import { replayActions } from '../../src/kernel/proof/action'
import { buildFregeTheory } from '../../src/theories'
import {
  associativityCarrierContent,
  commutativityCarrierContent,
  directCuts,
  rightIdentityCarrierContent,
  successorShiftCarrierContent,
} from '../../src/theories/arithmetic-support'
import { buildArithmeticStatements } from '../../src/theories/statements'

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

describe('relational Frege arithmetic proofs', () => {
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
      expect(actions.every((action) => action.steps.length === 1)).toBe(true)
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
    const theory = buildFregeTheory()
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
    const theory = buildFregeTheory()
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
    const theory = buildFregeTheory()
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
        expect(action.steps).toHaveLength(1)
        const [step] = action.steps
        if (step?.rule === 'theorem') {
          expect(precedingNames.has(step.name)).toBe(true)
        }
      }

      const forward = replayActions(
        theorem.lhs.diagram,
        theorem.actions,
        context,
        (_diagram, _actionIndex, stepIndex) => {
          expect(stepIndex).toBe(0)
        },
      )
      const backward = replayActions(
        theorem.rhs.diagram,
        theorem.backActions ?? [],
        context,
        (_diagram, _actionIndex, stepIndex) => {
          expect(stepIndex).toBe(0)
        },
        'backward',
      )
      expect(exploreForm(forward)).toBe(exploreForm(backward))
      context = registerTheorem(context, theorem)
    }
  })

  it('grounds each Nat property directly to its exact induction carrier', () => {
    const theory = buildFregeTheory()
    const expectedCarrier = [
      ['plusRightUnit', rightIdentityCarrierContent(), 2, 1],
      ['plusAssoc', associativityCarrierContent(), 1, 2],
      ['succShiftS', successorShiftCarrierContent(), 2, 1],
      ['plusComm', commutativityCarrierContent(), 2, 1],
    ] as const

    for (const [
      theoremName,
      carrier,
      captureCount,
      groundingCount,
    ] of expectedCarrier) {
      const theorem = theory.theorems.find(
        ({ name }) => name === theoremName,
      )
      expect(theorem, `theorem '${theoremName}'`).toBeDefined()
      const proven = theorem!
      const steps = [
        ...proven.actions,
        ...(proven.backActions ?? []),
      ].flatMap((action) => action.steps)
      const carrierGroundings = steps.filter((step) =>
        step.rule === 'wireJoin'
        && step.input.kind === 'relation'
        && exploreForm(
          step.input.content.diagram,
          step.input.content.boundary,
        ) === exploreForm(carrier.diagram, carrier.boundary))
      expect(carrierGroundings).toHaveLength(groundingCount)
      for (const grounding of carrierGroundings) {
        expect(
          grounding.rule === 'wireJoin'
          && grounding.input.kind === 'relation'
            ? grounding.input.parameters
            : [],
        ).toHaveLength(captureCount)
      }
      const rules = new Set(steps.map((step) => step.rule))
      for (const required of [
        'unfold',
        'iteration',
        'wireJoin',
        'deiteration',
        'doubleCutElim',
      ]) {
        expect(rules.has(required as typeof steps[number]['rule'])).toBe(true)
      }
    }
  })

  it('uses both associativity Nat premises causally', () => {
    const theory = buildFregeTheory()
    const theoremIndex = theory.theorems.findIndex(
      ({ name }) => name === 'plusAssoc',
    )
    const theorem = theory.theorems[theoremIndex]!
    const natPremises = Object.entries(theorem.rhs.diagram.nodes)
      .filter(([, node]) => node.kind === 'ref' && node.defId === 'nat')
    expect(natPremises).toHaveLength(2)
    const natNodeIds = new Set(natPremises.map(([nodeId]) => nodeId))
    const natUnfoldIds = (theorem.backActions ?? [])
      .flatMap((action) => action.steps)
      .filter((step) =>
        step.rule === 'unfold' && natNodeIds.has(step.nodeId))
      .map((step) => step.rule === 'unfold' ? step.nodeId : '')
    expect(new Set(natUnfoldIds)).toEqual(natNodeIds)

    const carrierForm = exploreForm(
      associativityCarrierContent().diagram,
      associativityCarrierContent().boundary,
    )
    const groundingActionIndexes = (theorem.backActions ?? [])
      .map((action, index) => action.steps.some((step) =>
        step.rule === 'wireJoin'
        && step.input.kind === 'relation'
        && exploreForm(
          step.input.content.diagram,
          step.input.content.boundary,
        ) === carrierForm)
        ? index
        : -1)
      .filter((index) => index >= 0)
    expect(groundingActionIndexes).toHaveLength(2)

    for (const removedIndex of groundingActionIndexes) {
      const withoutGrounding = {
        ...theorem,
        backActions: (theorem.backActions ?? []).filter(
          (_action, index) => index !== removedIndex,
        ),
      }
      expect(() => verifyTheory({
        relations: theory.relations,
        theorems: [
          ...theory.theorems.slice(0, theoremIndex),
          withoutGrounding,
        ],
      })).toThrow()
    }

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

  it('uses the commutativity-support Nat premise causally', () => {
    const theory = buildFregeTheory()
    const theoremIndex = theory.theorems.findIndex(
      ({ name }) => name === 'commutativityCarrierInductive',
    )
    const theorem = theory.theorems[theoremIndex]!
    const natPremises = Object.entries(theorem.rhs.diagram.nodes)
      .filter(([, node]) => node.kind === 'ref' && node.defId === 'nat')
    expect(natPremises).toHaveLength(1)
    const natNodeId = natPremises[0]![0]
    const unfoldIds = (theorem.backActions ?? [])
      .flatMap((action) => action.steps)
      .filter((step) => step.rule === 'unfold')
      .map((step) => step.rule === 'unfold' ? step.nodeId : '')
    expect(unfoldIds).toContain(natNodeId)

    const carrierForm = exploreForm(
      successorShiftCarrierContent().diagram,
      successorShiftCarrierContent().boundary,
    )
    const groundingActionIndexes = (theorem.backActions ?? [])
      .map((action, index) => action.steps.some((step) =>
        step.rule === 'wireJoin'
        && step.input.kind === 'relation'
        && exploreForm(
          step.input.content.diagram,
          step.input.content.boundary,
        ) === carrierForm
        && step.input.parameters.length === 2)
        ? index
        : -1)
      .filter((index) => index >= 0)
    expect(groundingActionIndexes).toHaveLength(1)

    const withoutGrounding = {
      ...theorem,
      backActions: (theorem.backActions ?? []).filter(
        (_action, index) => index !== groundingActionIndexes[0],
      ),
    }
    expect(() => verifyTheory({
      relations: theory.relations,
      theorems: [
        ...theory.theorems.slice(0, theoremIndex),
        withoutGrounding,
      ],
    })).toThrow()
  })

  it('uses the required earlier arithmetic results as causal citations', () => {
    const theory = buildFregeTheory()
    const citations = (theoremName: string): ReadonlySet<string> => {
      const theorem = theory.theorems.find(({ name }) => name === theoremName)
      expect(theorem, `theorem '${theoremName}'`).toBeDefined()
      return new Set([
        ...theorem!.actions,
        ...(theorem!.backActions ?? []),
      ].flatMap((action) => action.steps)
        .filter((step) => step.rule === 'theorem')
        .map((step) => step.name))
    }

    for (const required of ['zeroIsNat', 'succNat']) {
      expect(citations('oneIsNat')).toContain(required)
    }
    expect(citations('plusComm')).toContain(
      'commutativityCarrierInductive',
    )
    for (const required of [
      'plusLeftUnit',
      'rightIdentityCarrierInductive',
      'plusRightUnit',
      'successorShiftCarrierInductive',
      'succShiftS',
    ]) {
      expect(citations('commutativityCarrierInductive'))
        .toContain(required)
    }
  })
})
