import { describe, expect, it } from 'vitest'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { mkDiagramWithBoundary } from '../../../src/kernel/diagram/boundary'
import type { Diagram, WireId } from '../../../src/kernel/diagram/diagram'
import { exploreForm } from '../../../src/kernel/diagram/canonical/explore'
import { mkSelection } from '../../../src/kernel/diagram/subgraph/selection'
import { parseTerm } from '../../../src/kernel/term/parse'
import type { Theorem } from '../../../src/kernel/proof/theorem'
import { EMPTY_PROOF_CONTEXT, verifyTheory } from '../../../src/kernel/proof/context'
import { applyStep, applyStepWithReceipt, transportBoundary } from '../../../src/kernel/proof/step'
import { findDeiterationEvidence } from '../../../src/kernel/rules/iteration'

const closedIdentity = parseTerm('\\x. x')
const reflexive = { leftSteps: [], rightSteps: [] } as const

function expectDiscreteAliasReceipt(
  before: Diagram,
  result: ReturnType<typeof applyStepWithReceipt>,
  first: WireId,
  marker: WireId,
  second: WireId,
): void {
  expect(result.result.wires[first]).toBeDefined()
  expect(result.result.wires[second]).toBeDefined()
  expect(result.provenance.image(first)).toBe(first)
  expect(result.provenance.image(second)).toBe(second)
  expect(result.interface.image(first)).toBe(first)
  expect(result.interface.image(second)).toBe(second)
  expect(transportBoundary(result.interface, [first, marker, second, first]))
    .toEqual([first, marker, second, first])

  const addedAliases = Object.entries(result.result.nodes).filter(([id, node]) =>
    before.nodes[id] === undefined && node.kind === 'term' && node.freePorts.length === 1)
  expect(addedAliases).toHaveLength(1)
  const alias = addedAliases[0]![0]
  expect(result.result.wires[first]!.endpoints.some((endpoint) => endpoint.node === alias)).toBe(true)
  expect(result.result.wires[second]!.endpoints.some((endpoint) => endpoint.node === alias)).toBe(true)
}

describe('high-level attachment-alias materialization parity', () => {
  it('theorem replacement keeps distinct host identities for a repeated target boundary', () => {
    const left = new DiagramBuilder()
    const survivor = left.termNode(left.root, closedIdentity)
    const redundant = left.termNode(left.root, closedIdentity)
    const first = left.wire(left.root, [{ node: survivor, port: { kind: 'output' } }])
    const second = left.wire(left.root, [{ node: redundant, port: { kind: 'output' } }])
    const lhs = mkDiagramWithBoundary(left.build(), [first, second])

    const right = new DiagramBuilder()
    const retained = right.termNode(right.root, closedIdentity)
    const shared = right.wire(right.root, [{ node: retained, port: { kind: 'output' } }])
    const rhs = mkDiagramWithBoundary(right.build(), [shared, shared])
    const theorem: Theorem = {
      name: 'contract-to-local-alias',
      lhs,
      rhs,
      actions: [{
        label: 'contract equal closed witnesses',
        placements: [],
        steps: [{ rule: 'anchoredWireContract', redundant, survivor, certificate: reflexive }],
      }],
    }
    const context = verifyTheory({ relations: [], theorems: [theorem] })

    const host = new DiagramBuilder()
    const hostSurvivor = host.termNode(host.root, closedIdentity)
    const hostRedundant = host.termNode(host.root, closedIdentity)
    const hostFirst = host.wire(host.root, [{ node: hostSurvivor, port: { kind: 'output' } }])
    const hostSecond = host.wire(host.root, [{ node: hostRedundant, port: { kind: 'output' } }])
    const marker = host.wire(host.root, [])
    const diagram = host.build()
    const receipt = applyStepWithReceipt(diagram, {
      rule: 'theorem',
      name: theorem.name,
      at: {
        sel: { region: diagram.root, regions: [], nodes: [hostSurvivor, hostRedundant], wires: [] },
        args: [hostFirst, hostSecond],
      },
      direction: 'forward',
    }, context)

    expectDiscreteAliasReceipt(diagram, receipt, hostFirst, marker, hostSecond)
  })

  it('relation unfolding keeps distinct argument wires for a repeated body boundary', () => {
    const body = new DiagramBuilder()
    const bodyNode = body.termNode(body.root, closedIdentity)
    const repeated = body.wire(body.root, [{ node: bodyNode, port: { kind: 'output' } }])
    const relation = mkDiagramWithBoundary(body.build(), [repeated, repeated])
    const context = verifyTheory({ relations: [['Alias', relation]], theorems: [] })

    const host = new DiagramBuilder()
    const reference = host.ref(host.root, 'Alias', 2)
    const first = host.wire(host.root, [{ node: reference, port: { kind: 'arg', index: 0 } }])
    const second = host.wire(host.root, [{ node: reference, port: { kind: 'arg', index: 1 } }])
    const marker = host.wire(host.root, [])
    const diagram = host.build()
    const receipt = applyStepWithReceipt(diagram, { rule: 'relUnfold', node: reference }, context)

    expectDiscreteAliasReceipt(diagram, receipt, first, marker, second)
  })

  it('comprehension instantiation keeps distinct atom wires for a repeated comprehension boundary', () => {
    const body = new DiagramBuilder()
    const bodyNode = body.termNode(body.root, closedIdentity)
    const repeated = body.wire(body.root, [{ node: bodyNode, port: { kind: 'output' } }])
    const comprehension = mkDiagramWithBoundary(body.build(), [repeated, repeated])

    const host = new DiagramBuilder()
    const cut = host.cut(host.root)
    const bubble = host.bubble(cut, 2)
    const atom = host.atom(bubble, bubble)
    const first = host.wire(host.root, [{ node: atom, port: { kind: 'arg', index: 0 } }])
    const second = host.wire(host.root, [{ node: atom, port: { kind: 'arg', index: 1 } }])
    const marker = host.wire(host.root, [])
    const diagram = host.build()
    const receipt = applyStepWithReceipt(diagram, {
      rule: 'comprehensionInstantiate',
      bubble,
      comp: comprehension,
      attachments: [],
      binders: [],
    }, verifyTheory({ relations: [], theorems: [] }))

    expectDiscreteAliasReceipt(diagram, receipt, first, marker, second)
  })
})

describe('certified deiteration external-order parity', () => {
  it('rejects binder and attachment tampering before changing the source diagram', () => {
    const builder = new DiagramBuilder()
    const binder = builder.bubble(builder.root, 2)
    const justifier = builder.atom(binder, binder)
    const targetRegion = builder.cut(binder)
    const target = builder.atom(targetRegion, binder)
    const first = builder.wire(builder.root, [
      { node: justifier, port: { kind: 'arg', index: 0 } },
      { node: target, port: { kind: 'arg', index: 0 } },
    ])
    const second = builder.wire(builder.root, [
      { node: justifier, port: { kind: 'arg', index: 1 } },
      { node: target, port: { kind: 'arg', index: 1 } },
    ])
    const decoyBinder = builder.bubble(builder.root, 2)
    const diagram = builder.build()
    const selection = mkSelection(diagram, {
      region: targetRegion, regions: [], nodes: [target], wires: [],
    })
    const evidence = findDeiterationEvidence(diagram, selection, 100)
    expect(evidence.certificate.attachments).toEqual([first, second])
    const before = exploreForm(diagram)

    const binderEntry = [...evidence.certificate.binderMap][0]!
    const wrongBinder = {
      ...evidence.certificate,
      binderMap: new Map([[binderEntry[0], decoyBinder]]),
    }
    expect(() => applyStep(diagram, {
      rule: 'deiteration', sel: selection, justifier: evidence.justifier, certificate: wrongBinder,
    }, EMPTY_PROOF_CONTEXT)).toThrow(/external-binder map/)

    const wrongOrder = {
      ...evidence.certificate,
      attachments: [second, first],
    }
    expect(() => applyStep(diagram, {
      rule: 'deiteration', sel: selection, justifier: evidence.justifier, certificate: wrongOrder,
    }, EMPTY_PROOF_CONTEXT)).toThrow(/attachment|ordered attachments/)
    expect(exploreForm(diagram)).toBe(before)
  })
})
