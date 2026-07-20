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
    expect(verifyTheory({ relations: {}, theorems: [] })).toBe(EMPTY_PROOF_CONTEXT)
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
    ;(source as { name: string }).name = 'mutated-source'
    expect([...ctx.theorems.keys()]).toEqual(['stable'])
  })

  it('prevents prototype poisoning of authentic collection queries', () => {
    const ctx = registerTheorem(EMPTY_PROOF_CONTEXT, identity('stable'))
    const prototype = Object.getPrototypeOf(ctx.theorems) as Record<PropertyKey, unknown>
    expect(() => Object.defineProperty(prototype, 'get', {
      configurable: true,
      value: () => identity('forged'),
    })).toThrow()
    expect(() => Object.defineProperty(prototype, Symbol.iterator, {
      configurable: true,
      value: function* () { yield ['forged', identity('forged')] },
    })).toThrow()
    expect(ctx.theorems.get('forged')).toBeUndefined()
    expect([...ctx.theorems.keys()]).toEqual(['stable'])
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
      relations: { Bad: mkDiagramWithBoundary(nestedBuilder.build(), [nested]) },
      theorems: [],
    })).toThrowError(/boundary wire .* (?:is not|must be) scoped at the diagram root/)

    const rootBuilder = new DiagramBuilder()
    const rootWire = rootBuilder.wire(rootBuilder.root, [])
    const ctx = verifyTheory({
      relations: { Alias: mkDiagramWithBoundary(rootBuilder.build(), [rootWire, rootWire]) },
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
    expect(() => (step.certificate.regionMap as Map<string, string>).set('forged', 'forged')).toThrow()
    expect(step.certificate.regionMap.size).toBe(size)
    expect(() => ((action as { label: string }).label = 'mutated')).toThrow()
  })
})
