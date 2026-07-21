import { describe, expect, it } from 'vitest'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { mkDiagramWithBoundary } from '../../../src/kernel/diagram/boundary'
import type { ProofAction } from '../../../src/kernel/proof/action'
import { applyAction, replayActions } from '../../../src/kernel/proof/action'
import { composeActions } from '../../../src/kernel/proof/compose'
import {
  EMPTY_PROOF_CONTEXT,
  assertProofContext,
  extendRelations,
  registerTheorem,
  verifyTheory,
} from '../../../src/kernel/proof/context'
import type { ProofContext } from '../../../src/kernel/proof/context'
import { applyStep, applyStepWithReceipt, replayProof } from '../../../src/kernel/proof/step'
import { applyTheorem, checkTheorem } from '../../../src/kernel/proof/theorem'
import { buildFregeTheory } from '../../../src/theories/frege'

function emptyDiagram() {
  return new DiagramBuilder().build()
}

function identity(name: string) {
  const diagram = emptyDiagram()
  return { name, lhs: { diagram, boundary: [] }, rhs: { diagram, boundary: [] }, actions: [] }
}

describe('verified ProofContext authority', () => {
  it('uses one canonical empty context', () => {
    expect(verifyTheory({ relations: [], theorems: [] })).toBe(EMPTY_PROOF_CONTEXT)
    expect(() => assertProofContext(EMPTY_PROOF_CONTEXT)).not.toThrow()
    expect(replayProof(emptyDiagram(), [], EMPTY_PROOF_CONTEXT)).toEqual(emptyDiagram())
  })

  it('rejects structural and prototype forgeries at every public boundary, including zero-work paths', () => {
    const theorem = identity('identity')
    const unchecked = new Map([[theorem.name, theorem]])
    const lookalike = { theorems: unchecked, relations: new Map() } as unknown as ProofContext
    const prototype = Object.assign(
      Object.create(Object.getPrototypeOf(EMPTY_PROOF_CONTEXT)),
      { theorems: unchecked, relations: new Map() },
    ) as ProofContext
    const action: ProofAction = { label: 'noop-looking', steps: [], placements: [] }
    const diagram = emptyDiagram()
    const step = {
      rule: 'vacuousIntro',
      sel: { region: diagram.root, regions: [], nodes: [], wires: [] },
      arity: 0,
    } as const

    for (const forged of [lookalike, prototype]) {
      const calls = [
        () => applyStep(diagram, step, forged),
        () => applyStepWithReceipt(diagram, step, forged),
        () => applyAction(diagram, action, forged),
        () => replayActions(diagram, [], forged),
        () => replayProof(diagram, [], forged),
        () => composeActions(diagram, diagram, [], forged),
        () => checkTheorem(theorem, forged),
        () => applyTheorem(diagram, forged, 'identity', {
          sel: { region: diagram.root, regions: [], nodes: [], wires: [] },
          args: [],
        }, 'forward'),
      ]
      for (const call of calls) expect(call).toThrowError('invalid proof context')
    }
  })

  it('does not expose an authenticating constructor through an instance or prototype', () => {
    expect(Object.getPrototypeOf(EMPTY_PROOF_CONTEXT)).toBeNull()
    expect((EMPTY_PROOF_CONTEXT as unknown as { constructor?: unknown }).constructor).toBeUndefined()
    expect(() => {
      const Constructor = (EMPTY_PROOF_CONTEXT as unknown as { constructor: new (...args: unknown[]) => unknown }).constructor
      return new Constructor([], [])
    }).toThrow()
  })

  it('registers valid theorems incrementally without mutating prior contexts', () => {
    const first = registerTheorem(EMPTY_PROOF_CONTEXT, identity('first'))
    const second = registerTheorem(first, identity('second'))
    expect([...first.theorems.keys()]).toEqual(['first'])
    expect([...second.theorems.keys()]).toEqual(['first', 'second'])
    expect(EMPTY_PROOF_CONTEXT.theorems.size).toBe(0)
  })

  it('rejects malformed in-memory diagrams without a serialization round trip', () => {
    const diagram = emptyDiagram()
    const malformed = {
      ...diagram,
      regions: { ...diagram.regions, second: { kind: 'sheet' as const } },
    }
    expect(() => registerTheorem(EMPTY_PROOF_CONTEXT, {
      name: 'malformed-diagram',
      lhs: { diagram: malformed, boundary: [] },
      rhs: { diagram: malformed, boundary: [] },
      actions: [],
    })).toThrow(/sheet|root/i)
  })

  it('validates the direct theorem carrier without a serialization round trip', () => {
    const valid = identity('direct-carrier')
    expect(() => registerTheorem(EMPTY_PROOF_CONTEXT, {
      ...valid,
      name: 5,
    } as unknown as typeof valid)).toThrow(/name.*string/i)
    expect(() => registerTheorem(EMPTY_PROOF_CONTEXT, {
      ...valid,
      extra: true,
    } as unknown as typeof valid)).toThrow(/unknown field 'extra'/i)
    expect(() => registerTheorem(EMPTY_PROOF_CONTEXT, {
      ...valid,
      actions: {},
    } as unknown as typeof valid)).toThrow(/actions.*array/i)
    expect(() => registerTheorem(EMPTY_PROOF_CONTEXT, {
      ...valid,
      backActions: null,
    } as unknown as typeof valid)).toThrow(/backActions.*array/i)
  })

  it('does not expose mutable certified maps or mutable stored theorem data', () => {
    const source = identity('stable')
    const ctx = registerTheorem(EMPTY_PROOF_CONTEXT, source)
    expect(() => (ctx.theorems as Map<string, unknown>).set('forged', identity('forged'))).toThrow()
    expect(() => ((ctx.theorems.get('stable')!.actions as unknown[]) as unknown[]).push({})).toThrow()
    expect(() => ((ctx.theorems.get('stable') as unknown as { name: string }).name = 'forged')).toThrow()
    expect(() => ((ctx.theorems.get('stable') as unknown as { actions: unknown[] }).actions = [])).toThrow()
    ;(source as { name: string }).name = 'mutated-source'
    expect([...ctx.theorems.keys()]).toEqual(['stable'])
  })

  it('prevents prototype poisoning of authentic queries and certified execution', () => {
    const ctx = verifyTheory({
      relations: [['StableRelation', mkDiagramWithBoundary(emptyDiagram(), [])]],
      theorems: [identity('stable-theorem')],
    })
    const prototype = Object.getPrototypeOf(ctx.theorems) as Record<PropertyKey, unknown>
    expect(() => Object.defineProperty(prototype, 'get', {
      configurable: true,
      value: () => identity('forged'),
    })).toThrow()
    expect(() => Object.defineProperty(prototype, 'has', {
      configurable: true,
      value: () => false,
    })).toThrow()
    expect(() => Object.defineProperty(prototype, Symbol.iterator, {
      configurable: true,
      value: function* () { yield ['forged', identity('forged')] },
    })).toThrow()

    expect(ctx.theorems.get('forged')).toBeUndefined()
    expect(ctx.theorems.has('stable-theorem')).toBe(true)
    expect(ctx.relations.has('StableRelation')).toBe(true)
    expect([...ctx.theorems].map(([name]) => name)).toEqual(['stable-theorem'])
    expect([...ctx.relations].map(([name]) => name)).toEqual(['StableRelation'])

    const theoremHost = emptyDiagram()
    expect(applyTheorem(theoremHost, ctx, 'stable-theorem', {
      sel: { region: theoremHost.root, regions: [], nodes: [], wires: [] },
      args: [],
    }, 'forward')).toEqual(theoremHost)

    const relationHostBuilder = new DiagramBuilder()
    const relationRef = relationHostBuilder.ref(relationHostBuilder.root, 'StableRelation', 0)
    const relationHost = relationHostBuilder.build()
    expect(applyStep(relationHost, { rule: 'relUnfold', node: relationRef }, ctx)).toEqual(emptyDiagram())
  })

  it('ignores native Map and WeakSet prototype poisoning after module initialization', () => {
    const ctx = verifyTheory({
      relations: [['StableRelation', mkDiagramWithBoundary(emptyDiagram(), [])]],
      theorems: [identity('stable-theorem')],
    })
    const mapGet = Object.getOwnPropertyDescriptor(Map.prototype, 'get')!
    const mapHas = Object.getOwnPropertyDescriptor(Map.prototype, 'has')!
    const mapIterator = Object.getOwnPropertyDescriptor(Map.prototype, Symbol.iterator)!
    const weakSetHas = Object.getOwnPropertyDescriptor(WeakSet.prototype, 'has')!
    let observed: unknown
    let forgedRejected = false
    try {
      Object.defineProperty(Map.prototype, 'get', { configurable: true, value: () => identity('forged') })
      Object.defineProperty(Map.prototype, 'has', { configurable: true, value: () => false })
      Object.defineProperty(Map.prototype, Symbol.iterator, {
        configurable: true,
        value: function* () { yield ['forged', identity('forged')] },
      })
      Object.defineProperty(WeakSet.prototype, 'has', { configurable: true, value: () => true })
      assertProofContext(ctx)
      try {
        assertProofContext({ theorems: new Map(), relations: new Map() })
      } catch {
        forgedRejected = true
      }
      observed = {
        theorem: ctx.theorems.get('stable-theorem')?.name,
        relation: ctx.relations.has('StableRelation'),
        theoremNames: [...ctx.theorems].map(([name]) => name),
        relationNames: [...ctx.relations].map(([name]) => name),
      }
    } finally {
      Object.defineProperty(Map.prototype, 'get', mapGet)
      Object.defineProperty(Map.prototype, 'has', mapHas)
      Object.defineProperty(Map.prototype, Symbol.iterator, mapIterator)
      Object.defineProperty(WeakSet.prototype, 'has', weakSetHas)
    }
    expect(forgedRejected).toBe(true)
    expect(observed).toEqual({
      theorem: 'stable-theorem',
      relation: true,
      theoremNames: ['stable-theorem'],
      relationNames: ['StableRelation'],
    })
  })

  it('rejects executable, unsupported, and cyclic theorem schema carriers', () => {
    const functionActions = {
      ...identity('function-actions'),
      actions: (() => []) as unknown as readonly ProofAction[],
    }
    expect(() => registerTheorem(EMPTY_PROOF_CONTEXT, functionActions)).toThrow(/unsupported function value/)

    const certificate = { leftSteps: [] as unknown[], rightSteps: [] as unknown[] }
    certificate.leftSteps.push(certificate)
    const cyclic = {
      ...identity('cyclic-certificate'),
      actions: [{
        label: 'cyclic',
        steps: [{ rule: 'anchoredWireContract', redundant: 'n0', survivor: 'n1', certificate }],
        placements: [],
      }],
    } as unknown as ReturnType<typeof identity>
    expect(() => registerTheorem(EMPTY_PROOF_CONTEXT, cyclic)).toThrow(/cyclic values are not supported/)
  })

  it('owns immutable relation snapshots and preserves valid incremental order', () => {
    const baseBuilder = new DiagramBuilder()
    const baseWire = baseBuilder.wire(baseBuilder.root, [])
    const baseSource = mkDiagramWithBoundary(baseBuilder.build(), [baseWire])
    const first = extendRelations(EMPTY_PROOF_CONTEXT, [['Base', baseSource]])

    const aliasBuilder = new DiagramBuilder()
    const aliasNode = aliasBuilder.ref(aliasBuilder.root, 'Base', 1)
    const aliasWire = aliasBuilder.wire(aliasBuilder.root, [{ node: aliasNode, port: { kind: 'arg', index: 0 } }])
    const second = extendRelations(first, [['Alias', mkDiagramWithBoundary(aliasBuilder.build(), [aliasWire])]])
    expect([...second.relations.keys()]).toEqual(['Base', 'Alias'])

    expect(() => (second.relations as Map<string, unknown>).delete('Base')).toThrow()
    const stored = second.relations.get('Base')!
    expect(() => ((stored.diagram.wires[baseWire] as { scope: string }).scope = 'forged')).toThrow()
    ;(baseSource.diagram.wires[baseWire] as { scope: string }).scope = 'mutated-source'
    expect(stored.diagram.wires[baseWire]!.scope).toBe(stored.diagram.root)
  })

  it('rejects a relation boundary below the root while preserving repeated root positions', () => {
    const nestedBuilder = new DiagramBuilder()
    const cut = nestedBuilder.cut(nestedBuilder.root)
    const nested = nestedBuilder.wire(cut, [])
    expect(() => verifyTheory({
      relations: [['Bad', mkDiagramWithBoundary(nestedBuilder.build(), [nested])]],
      theorems: [],
    })).toThrowError(/boundary wire .* (?:is not|must be) scoped at the diagram root/)

    const rootBuilder = new DiagramBuilder()
    const rootWire = rootBuilder.wire(rootBuilder.root, [])
    const ctx = verifyTheory({
      relations: [['Alias', mkDiagramWithBoundary(rootBuilder.build(), [rootWire, rootWire])]],
      theorems: [],
    })
    expect(ctx.relations.get('Alias')!.boundary).toEqual([rootWire, rootWire])
  })

  it('hardens nested stored actions and occurrence-certificate maps', () => {
    const source = buildFregeTheory()
    const ctx = verifyTheory(source)
    const theorem = [...ctx.theorems.values()].find((candidate) =>
      candidate.actions.some((action) => action.steps.some((step) => step.rule === 'deiteration')),
    )!
    const action = theorem.actions.find((candidate) => candidate.steps.some((step) => step.rule === 'deiteration'))!
    const step = action.steps.find((candidate) => candidate.rule === 'deiteration')!
    if (step.rule !== 'deiteration') throw new Error('expected deiteration step')
    const size = step.certificate.regionMap.size
    const sourceTheorem = source.theorems.find((candidate) => candidate.name === theorem.name)!
    const sourceStep = sourceTheorem.actions.flatMap((candidate) => candidate.steps)
      .find((candidate) => candidate.rule === 'deiteration')!
    if (sourceStep.rule !== 'deiteration') throw new Error('expected source deiteration step')
    ;(sourceStep.certificate.regionMap as Map<string, string>).set('source-forged', 'source-forged')
    expect(step.certificate.regionMap.has('source-forged')).toBe(false)
    expect(() => checkTheorem(theorem, ctx)).not.toThrow()
    expect(() => (step.certificate.regionMap as Map<string, string>).set('forged', 'forged')).toThrow()
    expect(step.certificate.regionMap.size).toBe(size)
    expect(() => ((action as { label: string }).label = 'mutated')).toThrow()
  })
})
