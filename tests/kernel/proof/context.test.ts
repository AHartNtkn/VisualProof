import { describe, expect, it } from 'vitest'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { derivedScope } from '../../../src/kernel/diagram/regions'
import { pointAssembly } from '../../../src/kernel/rules/identity-rules'
import { mkDiagramWithBoundary } from '../../../src/kernel/diagram/boundary'
import { relSig, IOTA } from '../../../src/kernel/diagram/sig'
import { mkSelection } from '../../../src/kernel/diagram/subgraph/selection'
import { applyIteration, applyDeiteration, findDeiterationEvidence } from '../../../src/kernel/rules/iteration'
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
import type { ProofContext, Theory } from '../../../src/kernel/proof/context'
import { applyStep, applyStepWithReceipt, replayProof } from '../../../src/kernel/proof/step'
import { applyTheorem, checkTheorem, type Theorem } from '../../../src/kernel/proof/theorem'

/** A small theory whose only theorem's action is a deiteration step: enough
 * to exercise nested-map hardening (regionMap, occurrence certificates)
 * without depending on any external theory file. */
function deiterationTheory(): Theory {
  const h = new DiagramBuilder()
  const c1 = h.cut(h.root)
  const inner = h.cut(c1)
  h.atom(inner, relSig([]))
  const target = h.cut(c1)
  const d0 = h.build()
  const sel = mkSelection(d0, { region: c1, regions: [inner], nodes: [], wires: [] })
  const iterated = applyIteration(d0, sel, target)
  const copyInner = Object.entries(iterated.regions).find(([id, r]) =>
    r.kind === 'cut' && r.parent === target && id !== inner)![0]
  const selCopy = mkSelection(iterated, { region: target, regions: [copyInner], nodes: [], wires: [] })
  const evidence = findDeiterationEvidence(iterated, selCopy)
  const afterDeiteration = applyDeiteration(iterated, selCopy, evidence.justifier, evidence.certificate)
  const action: ProofAction = {
    label: 'deiterate the copy',
    placements: [],
    steps: [{
      rule: 'deiteration',
      sel: selCopy,
      justifier: evidence.justifier,
      certificate: evidence.certificate,
      }],
  }
  const theorem: Theorem = {
    name: 'deiterate-copy',
    lhs: mkDiagramWithBoundary(iterated, []),
    rhs: mkDiagramWithBoundary(afterDeiteration, []),
    actions: [action],
  }
  return { relations: [], theorems: [theorem] }
}

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
      rule: 'vacuity',
      direction: 'insert',
      assembly: pointAssembly('point', diagram.root, IOTA),
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
    const relationRef = relationHostBuilder.ref(relationHostBuilder.root, 'StableRelation', relSig([]))
    const relationHost = relationHostBuilder.build()
    expect(applyStep(relationHost, { rule: 'unfold', nodeId: relationRef }, ctx)).toEqual(emptyDiagram())
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

    const wires: unknown[] = []
    wires.push(wires)
    const cyclic = {
      ...identity('cyclic-wires'),
      actions: [{
        label: 'cyclic',
        steps: [{ rule: 'identityInsert', region: 'r0', wires }],
        placements: [],
      }],
    } as unknown as ReturnType<typeof identity>
    expect(() => registerTheorem(EMPTY_PROOF_CONTEXT, cyclic)).toThrow(/cyclic values are not supported/)
  })

  it('owns immutable relation snapshots and preserves valid incremental order', () => {
    const baseBuilder = new DiagramBuilder()
    const baseWire = baseBuilder.wire([])
    const baseSource = baseBuilder.buildOpen([baseWire])
    const first = extendRelations(EMPTY_PROOF_CONTEXT, [['Base', baseSource]])

    const aliasBuilder = new DiagramBuilder()
    const aliasNode = aliasBuilder.ref(aliasBuilder.root, 'Base', relSig([IOTA]))
    const aliasWire = aliasBuilder.wire([{ node: aliasNode, port: { kind: 'arg', index: 0 } }])
    const second = extendRelations(first, [['Alias', aliasBuilder.buildOpen([aliasWire])]])
    expect([...second.relations.keys()]).toEqual(['Base', 'Alias'])

    expect(() => (second.relations as Map<string, unknown>).delete('Base')).toThrow()
    const stored = second.relations.get('Base')!
    expect(() => ((stored.diagram.wires[baseWire] as { sig: unknown }).sig = 'forged'))
      .toThrow()
    ;(baseSource.diagram.wires[baseWire] as { sig: unknown }).sig = 'mutated-source'
    expect(stored.diagram.wires[baseWire]!.sig).toEqual(IOTA)
    expect(derivedScope(stored.diagram, baseWire, stored.boundary))
      .toBe(stored.diagram.root)
  })

  it('rejects a reference whose arity matches but nested signature differs', () => {
    const baseBuilder = new DiagramBuilder()
    const nested = relSig([IOTA])
    const baseWire = baseBuilder.wire([], nested)
    const base = baseBuilder.buildOpen([baseWire])
    const first = extendRelations(EMPTY_PROOF_CONTEXT, [['Base', base]])

    const aliasBuilder = new DiagramBuilder()
    const alias = aliasBuilder.ref(aliasBuilder.root, 'Base', relSig([IOTA]))
    const aliasWire = aliasBuilder.wire([
      { node: alias, port: { kind: 'arg', index: 0 } },
    ], IOTA)

    expect(() => extendRelations(first, [[
      'Alias',
      aliasBuilder.buildOpen([aliasWire]),
    ]])).toThrowError(
      "relation 'Alias' body: reference node 'n0' signature '(i)' "
      + "does not match definition 'Base' signature '((i))'",
    )
  })

  it('roots a relation boundary however deep its other ends sit, and preserves repeated root positions', () => {
    // A formal whose only node end is a pin inside a cut is still exposed at
    // the frame, and the frame exit is a root incidence — so the formal is
    // root-quantified and the body is a well-formed relation.
    const nestedBuilder = new DiagramBuilder()
    const cut = nestedBuilder.cut(nestedBuilder.root)
    const nested = nestedBuilder.wire([])
    nestedBuilder.pin(nested, cut)
    const nestedBody = nestedBuilder.buildOpen([nested])
    expect(derivedScope(nestedBody.diagram, nested)).toBe(cut)
    expect(derivedScope(nestedBody.diagram, nested, nestedBody.boundary))
      .toBe(nestedBody.diagram.root)

    const nestedCtx = verifyTheory({
      relations: [['Deep', nestedBody]],
      theorems: [],
    })
    expect(nestedCtx.relations.get('Deep')!.boundary).toEqual([nested])

    const rootBuilder = new DiagramBuilder()
    const rootWire = rootBuilder.wire([])
    const ctx = verifyTheory({
      relations: [['Alias', rootBuilder.buildOpen([rootWire, rootWire])]],
      theorems: [],
    })
    expect(ctx.relations.get('Alias')!.boundary).toEqual([rootWire, rootWire])
  })

  it('hardens nested stored actions and occurrence-certificate maps', () => {
    const source = deiterationTheory()
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
