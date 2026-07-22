import { describe, expect, it } from 'vitest'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { mkDiagramWithBoundary } from '../../../src/kernel/diagram/boundary'
import type { Diagram, WireId } from '../../../src/kernel/diagram/diagram'
import { relSig, TERM } from '../../../src/kernel/diagram/sig'
import { exploreForm } from '../../../src/kernel/diagram/canonical/explore'
import { mkSelection } from '../../../src/kernel/diagram/subgraph/selection'
import { parseTerm } from '../../../src/kernel/term/parse'
import type { Theorem } from '../../../src/kernel/proof/theorem'
import { EMPTY_PROOF_CONTEXT, verifyTheory } from '../../../src/kernel/proof/context'
import { applyStep, applyStepWithReceipt, transportBoundary } from '../../../src/kernel/proof/step'
import { findDeiterationEvidence } from '../../../src/kernel/rules/iteration'
import { applyBodyAttach } from '../../../src/kernel/rules/body'

const arity2 = relSig([TERM, TERM])

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
    const reference = host.ref(host.root, 'Alias', arity2)
    const first = host.wire(host.root, [{ node: reference, port: { kind: 'arg', index: 0 } }])
    const second = host.wire(host.root, [{ node: reference, port: { kind: 'arg', index: 1 } }])
    const marker = host.wire(host.root, [])
    const diagram = host.build()
    const receipt = applyStepWithReceipt(diagram, { rule: 'unfold', nodeId: reference }, context)

    expectDiscreteAliasReceipt(diagram, receipt, first, marker, second)
  })

  it('comprehension instantiation keeps distinct atom wires for a repeated comprehension boundary', () => {
    const body = new DiagramBuilder()
    const bodyNode = body.termNode(body.root, closedIdentity)
    const repeated = body.wire(body.root, [{ node: bodyNode, port: { kind: 'output' } }])
    const comprehension = mkDiagramWithBoundary(body.build(), [repeated, repeated])

    const host = new DiagramBuilder()
    const cut = host.cut(host.root)
    const atom = host.atom(cut, arity2)
    const headWire = host.wire(cut, [{ node: atom, port: { kind: 'head' } }], arity2)
    const first = host.wire(host.root, [{ node: atom, port: { kind: 'arg', index: 0 } }])
    const second = host.wire(host.root, [{ node: atom, port: { kind: 'arg', index: 1 } }])
    const marker = host.wire(host.root, [])
    const built = host.build()
    // Witnessing the relational head wire with a concrete comprehension IS
    // instantiation in the sig model (bodyAttach); the metered step is the
    // materializing unfold that follows.
    const diagram = applyBodyAttach(built, headWire, comprehension, [], 'forward')
    const receipt = applyStepWithReceipt(diagram, { rule: 'unfold', nodeId: atom }, verifyTheory({ relations: [], theorems: [] }))

    expectDiscreteAliasReceipt(diagram, receipt, first, marker, second)
  })
})

describe('certified deiteration external-order parity', () => {
  // Successor of the old binder-tampering half of this test: there is no
  // binder machinery in the sig model (extractSubgraph's doc comment), so a
  // relation's identity is carried entirely by its head wire — an ordinary
  // attachment. This still covers the surviving concern: tampering with the
  // certificate's ordered attachments is refused before the source mutates.
  it('rejects attachment tampering before changing the source diagram', () => {
    const builder = new DiagramBuilder()
    const outer = builder.cut(builder.root)
    const justifier = builder.atom(outer, arity2)
    const targetRegion = builder.cut(outer)
    const target = builder.atom(targetRegion, arity2)
    const headWire = builder.wire(outer, [
      { node: justifier, port: { kind: 'head' } },
      { node: target, port: { kind: 'head' } },
    ], arity2)
    const first = builder.wire(outer, [
      { node: justifier, port: { kind: 'arg', index: 0 } },
      { node: target, port: { kind: 'arg', index: 0 } },
    ])
    const second = builder.wire(outer, [
      { node: justifier, port: { kind: 'arg', index: 1 } },
      { node: target, port: { kind: 'arg', index: 1 } },
    ])
    const diagram = builder.build()
    const selection = mkSelection(diagram, {
      region: targetRegion, regions: [], nodes: [target], wires: [],
    })
    const evidence = findDeiterationEvidence(diagram, selection, 100)
    expect(new Set(evidence.certificate.attachments)).toEqual(new Set([headWire, first, second]))
    const before = exploreForm(diagram)

    const wrongOrder = {
      ...evidence.certificate,
      attachments: [...evidence.certificate.attachments].reverse(),
    }
    expect(() => applyStep(diagram, {
      rule: 'deiteration', sel: selection, justifier: evidence.justifier, certificate: wrongOrder,
    }, EMPTY_PROOF_CONTEXT)).toThrow(/attachment|ordered attachments/)
    expect(exploreForm(diagram)).toBe(before)
  })
})
