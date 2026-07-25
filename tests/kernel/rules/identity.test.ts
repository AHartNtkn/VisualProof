import { describe, expect, it } from 'vitest'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import type { Diagram, NodeId, WireId } from '../../../src/kernel/diagram/diagram'
import { exploreForm } from '../../../src/kernel/diagram/canonical/explore'
import { IOTA, relSig } from '../../../src/kernel/diagram/sig'
import { extractSubgraph } from '../../../src/kernel/diagram/subgraph/extract'
import { mkSelection, type SubgraphSelection } from '../../../src/kernel/diagram/subgraph/selection'
import { applyErasure } from '../../../src/kernel/rules/erasure'
import {
  applyIdentityContradiction,
  applyIdentityInsertion,
  type IdentityContradictionEvidence,
} from '../../../src/kernel/rules/identity'
import {
  applyDeiteration,
  applyIteration,
  findDeiterationEvidence,
  type IdentityRetarget,
} from '../../../src/kernel/rules/iteration'
import * as publicRules from '../../../src/kernel/rules/index'

type IdentityNode = Extract<Diagram['nodes'][NodeId], { kind: 'identity' }>

function identityNodes(
  diagram: Diagram,
): Array<[NodeId, IdentityNode]> {
  return Object.entries(diagram.nodes)
    .filter((entry): entry is [NodeId, IdentityNode] =>
      entry[1].kind === 'identity')
}

function boundaryOf(diagram: Diagram, selection: SubgraphSelection, wire: WireId): number {
  const boundary = extractSubgraph(diagram, selection).attachments.indexOf(wire)
  if (boundary < 0) throw new Error(`fixture wire '${wire}' is not an extracted boundary`)
  return boundary
}

function hasArgEndpoint(diagram: Diagram, wire: WireId, node: NodeId, index: number): boolean {
  return diagram.wires[wire]!.endpoints.some(
    (endpoint) =>
      endpoint.node === node
      && endpoint.port.kind === 'arg'
      && endpoint.port.index === index,
  )
}

function substitutionHost(source: 'from' | 'to' = 'from') {
  const builder = new DiagramBuilder()
  const ancestor = builder.cut(builder.root)
  const target = builder.cut(ancestor)
  const identity = builder.identity(ancestor, IOTA, 2)
  const atom = builder.atom(ancestor, relSig([IOTA]))
  const from = builder.wire(builder.root, [
    { node: identity, port: { kind: 'identity', index: 0 } },
    ...(source === 'from' ? [{ node: atom, port: { kind: 'arg' as const, index: 0 } }] : []),
  ])
  const to = builder.wire(builder.root, [
    { node: identity, port: { kind: 'identity', index: 1 } },
    ...(source === 'to' ? [{ node: atom, port: { kind: 'arg' as const, index: 0 } }] : []),
  ])
  const unlinked = builder.wire(builder.root, [])
  const mismatched = builder.wire(builder.root, [], relSig([]))
  const diagram = builder.build()
  const selection = mkSelection(diagram, {
    region: ancestor,
    regions: [],
    nodes: [atom],
    wires: [],
  })
  const sourceWire = source === 'from' ? from : to
  const destinationWire = source === 'from' ? to : from
  const retarget: IdentityRetarget = {
    boundary: boundaryOf(diagram, selection, sourceWire),
    identity,
    from: sourceWire,
    to: destinationWire,
  }
  return {
    diagram,
    ancestor,
    target,
    identity,
    atom,
    from,
    to,
    unlinked,
    mismatched,
    selection,
    retarget,
  }
}

function copiedAtom(diagram: Diagram, region: string, original: NodeId): NodeId {
  const copy = Object.entries(diagram.nodes).find(
    ([nodeId, node]) => nodeId !== original && node.kind === 'atom' && node.region === region,
  )
  if (copy === undefined) throw new Error(`fixture has no copied atom in '${region}'`)
  return copy[0]
}

describe('identity Rules 1–3 are canonicalizer-owned', () => {
  it('drops an identity whose storage incidences all name one wire', () => {
    const builder = new DiagramBuilder()
    const identity = builder.identity(builder.root, IOTA, 2)
    const wire = builder.wire(builder.root, [
      { node: identity, port: { kind: 'identity', index: 0 } },
      { node: identity, port: { kind: 'identity', index: 1 } },
    ])

    const diagram = builder.build()

    expect(diagram.nodes[identity]).toBeUndefined()
    expect(diagram.wires[wire]).toBeDefined()
  })

  it('collapses an unconditional same-scope identity into one wire', () => {
    const builder = new DiagramBuilder()
    const cut = builder.cut(builder.root)
    const identity = builder.identity(cut, IOTA, 2)
    const left = builder.wire(cut, [
      { node: identity, port: { kind: 'identity', index: 0 } },
    ])
    const right = builder.wire(cut, [
      { node: identity, port: { kind: 'identity', index: 1 } },
    ])

    const diagram = builder.build()

    expect(diagram.nodes[identity]).toBeUndefined()
    expect(Object.keys(diagram.wires)).toEqual([left])
    expect(diagram.wires[right]).toBeUndefined()
  })

  it('fuses touching same-region identities without a rule-layer rewrite', () => {
    const builder = new DiagramBuilder()
    const cut = builder.cut(builder.root)
    const first = builder.identity(cut, IOTA, 2)
    const second = builder.identity(cut, IOTA, 2)
    builder.wire(builder.root, [
      { node: first, port: { kind: 'identity', index: 0 } },
    ])
    builder.wire(builder.root, [
      { node: first, port: { kind: 'identity', index: 1 } },
      { node: second, port: { kind: 'identity', index: 0 } },
    ])
    builder.wire(builder.root, [
      { node: second, port: { kind: 'identity', index: 1 } },
    ])

    const diagram = builder.build()
    const identities = identityNodes(diagram)

    expect(identities).toHaveLength(1)
    expect(identities[0]![0]).toBe(first)
    expect(identities[0]![1].arity).toBe(3)
  })
})

describe('Rule 4: inherited identity insertion and ordinary erasure', () => {
  it('inserts an identity over distinct same-signature wires visible in a negative region', () => {
    const builder = new DiagramBuilder()
    const cut = builder.cut(builder.root)
    const left = builder.wire(builder.root, [])
    const right = builder.wire(builder.root, [])
    const diagram = builder.build()

    const inserted = applyIdentityInsertion(diagram, cut, [left, right])
    const identities = identityNodes(inserted)

    expect(identities).toHaveLength(1)
    expect(identities[0]![1]).toMatchObject({ region: cut, sig: IOTA, arity: 2 })
    expect(inserted.wires[left]!.endpoints).toContainEqual({
      node: identities[0]![0],
      port: { kind: 'identity', index: 0 },
    })
    expect(inserted.wires[right]!.endpoints).toContainEqual({
      node: identities[0]![0],
      port: { kind: 'identity', index: 1 },
    })
  })

  it('lets canonicalization eliminate a same-scope inserted identity', () => {
    const builder = new DiagramBuilder()
    const cut = builder.cut(builder.root)
    const left = builder.wire(cut, [])
    const right = builder.wire(cut, [])
    const diagram = builder.build()

    const inserted = applyIdentityInsertion(diagram, cut, [left, right])

    expect(identityNodes(inserted)).toHaveLength(0)
    expect(Object.keys(inserted.wires)).toHaveLength(1)
  })

  it('rejects positive insertion even if a caller supplies the removed backward orientation', () => {
    const builder = new DiagramBuilder()
    const left = builder.wire(builder.root, [])
    const right = builder.wire(builder.root, [])
    const diagram = builder.build()
    const invokeLegacyShape = applyIdentityInsertion as unknown as (
      d: Diagram,
      region: string,
      wires: readonly WireId[],
      orientation: string,
    ) => Diagram

    expect(() => applyIdentityInsertion(diagram, diagram.root, [left, right]))
      .toThrowError(/identity insertion requires a negative region/)
    expect(() => invokeLegacyShape(diagram, diagram.root, [left, right], 'backward'))
      .toThrowError(/identity insertion requires a negative region/)
  })

  it('rejects duplicate, mismatched-signature, and invisible insertion wires', () => {
    const builder = new DiagramBuilder()
    const cut = builder.cut(builder.root)
    const child = builder.cut(cut)
    const visible = builder.wire(builder.root, [])
    const relation = builder.wire(builder.root, [], relSig([]))
    const hidden = builder.wire(child, [])
    const diagram = builder.build()

    expect(() => applyIdentityInsertion(diagram, cut, [visible]))
      .toThrowError(/at least two distinct wires/)
    expect(() => applyIdentityInsertion(diagram, cut, [visible, visible]))
      .toThrowError(/distinct wires/)
    expect(() => applyIdentityInsertion(diagram, cut, [visible, relation]))
      .toThrowError(/same signature/)
    expect(() => applyIdentityInsertion(diagram, cut, [visible, hidden]))
      .toThrowError(/not visible/)
  })

  it('erases an identity only through ordinary positive erasure', () => {
    const builder = new DiagramBuilder()
    const outer = builder.cut(builder.root)
    const positive = builder.cut(outer)
    const identity = builder.identity(positive, IOTA, 2)
    const left = builder.wire(builder.root, [
      { node: identity, port: { kind: 'identity', index: 0 } },
    ])
    const right = builder.wire(builder.root, [
      { node: identity, port: { kind: 'identity', index: 1 } },
    ])
    const diagram = builder.build()
    const selection = mkSelection(diagram, {
      region: positive,
      regions: [],
      nodes: [identity],
      wires: [],
    })

    const erased = applyErasure(diagram, selection)

    expect(erased.nodes[identity]).toBeUndefined()
    expect(erased.wires[left]!.endpoints).toEqual([])
    expect(erased.wires[right]!.endpoints).toEqual([])
  })
})

describe('Rule 5: explicit endpoint-level equals-for-equals evidence', () => {
  it('retargets exactly the named atom argument from an outer wire to an equal wire', () => {
    const host = substitutionHost()

    const iterated = applyIteration(
      host.diagram,
      host.selection,
      host.target,
      [host.retarget],
    )
    const copy = copiedAtom(iterated, host.target, host.atom)

    expect(hasArgEndpoint(iterated, host.to, copy, 0)).toBe(true)
    expect(hasArgEndpoint(iterated, host.from, copy, 0)).toBe(false)
    expect(hasArgEndpoint(iterated, host.from, host.atom, 0)).toBe(true)
  })

  it('supports symmetry by retargeting in the reverse wire direction', () => {
    const host = substitutionHost('to')

    const iterated = applyIteration(
      host.diagram,
      host.selection,
      host.target,
      [host.retarget],
    )
    const copy = copiedAtom(iterated, host.target, host.atom)

    expect(hasArgEndpoint(iterated, host.from, copy, 0)).toBe(true)
    expect(hasArgEndpoint(iterated, host.to, host.atom, 0)).toBe(true)
  })

  it('retargets multiple named boundary positions without changing the head attachment', () => {
    const builder = new DiagramBuilder()
    const ancestor = builder.cut(builder.root)
    const target = builder.cut(ancestor)
    const firstIdentity = builder.identity(ancestor, IOTA, 2)
    const secondIdentity = builder.identity(ancestor, IOTA, 2)
    const atom = builder.atom(ancestor, relSig([IOTA, IOTA]))
    const firstFrom = builder.wire(builder.root, [
      { node: firstIdentity, port: { kind: 'identity', index: 0 } },
      { node: atom, port: { kind: 'arg', index: 0 } },
    ])
    const firstTo = builder.wire(builder.root, [
      { node: firstIdentity, port: { kind: 'identity', index: 1 } },
    ])
    const secondFrom = builder.wire(builder.root, [
      { node: secondIdentity, port: { kind: 'identity', index: 0 } },
      { node: atom, port: { kind: 'arg', index: 1 } },
    ])
    const secondTo = builder.wire(builder.root, [
      { node: secondIdentity, port: { kind: 'identity', index: 1 } },
    ])
    const diagram = builder.build()
    const selection = mkSelection(diagram, {
      region: ancestor,
      regions: [],
      nodes: [atom],
      wires: [],
    })
    const extracted = extractSubgraph(diagram, selection)
    const untouched = extracted.attachments.find(
      (wire) => wire !== firstFrom && wire !== secondFrom,
    )!
    const retargets: IdentityRetarget[] = [
      {
        boundary: boundaryOf(diagram, selection, firstFrom),
        identity: firstIdentity,
        from: firstFrom,
        to: firstTo,
      },
      {
        boundary: boundaryOf(diagram, selection, secondFrom),
        identity: secondIdentity,
        from: secondFrom,
        to: secondTo,
      },
    ]

    const iterated = applyIteration(diagram, selection, target, retargets)
    const copy = copiedAtom(iterated, target, atom)

    expect(hasArgEndpoint(iterated, firstTo, copy, 0)).toBe(true)
    expect(hasArgEndpoint(iterated, secondTo, copy, 1)).toBe(true)
    expect(iterated.wires[untouched]!.endpoints.some((endpoint) => endpoint.node === copy))
      .toBe(true)
  })

  it('round-trips retargeted iteration through exact deiteration evidence', () => {
    const host = substitutionHost()
    const iterated = applyIteration(
      host.diagram,
      host.selection,
      host.target,
      [host.retarget],
    )
    const copy = copiedAtom(iterated, host.target, host.atom)
    const copySelection = mkSelection(iterated, {
      region: host.target,
      regions: [],
      nodes: [copy],
      wires: [],
    })

    const evidence = findDeiterationEvidence(
      iterated,
      copySelection,
      10_000,
      [host.retarget],
    )
    const restored = applyDeiteration(
      iterated,
      copySelection,
      evidence.justifier,
      evidence.certificate,
      [host.retarget],
    )

    expect(exploreForm(restored)).toBe(exploreForm(host.diagram))
  })

  it('rejects wrong identity IDs, unlinked wires, and signature mismatches', () => {
    const host = substitutionHost()

    expect(() => applyIteration(host.diagram, host.selection, host.target, [{
      ...host.retarget,
      identity: host.atom,
    }])).toThrowError(/does not name an identity node/)
    expect(() => applyIteration(host.diagram, host.selection, host.target, [{
      ...host.retarget,
      to: host.unlinked,
    }])).toThrowError(/does not contain both/)
    expect(() => applyIteration(host.diagram, host.selection, host.target, [{
      ...host.retarget,
      to: host.mismatched,
    }])).toThrowError(/signature/)
  })

  it('rejects unsafe, duplicate, and mismatched boundary positions', () => {
    const host = substitutionHost()
    const attachments = extractSubgraph(host.diagram, host.selection).attachments
    const otherBoundary = attachments.findIndex((wire) => wire !== host.from)

    expect(() => applyIteration(host.diagram, host.selection, host.target, [{
      ...host.retarget,
      boundary: -1,
    }])).toThrowError(/safe boundary index/)
    expect(() => applyIteration(host.diagram, host.selection, host.target, [{
      ...host.retarget,
      boundary: otherBoundary,
    }])).toThrowError(/source attachment/)
    expect(() => applyIteration(host.diagram, host.selection, host.target, [
      host.retarget,
      host.retarget,
    ])).toThrowError(/duplicate retarget boundary/)
  })

  it('rejects an identity that does not dominate the copy region', () => {
    const builder = new DiagramBuilder()
    const source = builder.cut(builder.root)
    const target = builder.cut(source)
    const sibling = builder.cut(builder.root)
    const identity = builder.identity(sibling, IOTA, 2)
    const atom = builder.atom(source, relSig([IOTA]))
    const from = builder.wire(builder.root, [
      { node: identity, port: { kind: 'identity', index: 0 } },
      { node: atom, port: { kind: 'arg', index: 0 } },
    ])
    const to = builder.wire(builder.root, [
      { node: identity, port: { kind: 'identity', index: 1 } },
    ])
    const diagram = builder.build()
    const selection = mkSelection(diagram, {
      region: source,
      regions: [],
      nodes: [atom],
      wires: [],
    })

    expect(() => applyIteration(diagram, selection, target, [{
      boundary: boundaryOf(diagram, selection, from),
      identity,
      from,
      to,
    }])).toThrowError(/does not dominate/)
  })

  it('rejects reversed deiteration source/target evidence', () => {
    const host = substitutionHost()
    const iterated = applyIteration(
      host.diagram,
      host.selection,
      host.target,
      [host.retarget],
    )
    const copy = copiedAtom(iterated, host.target, host.atom)
    const copySelection = mkSelection(iterated, {
      region: host.target,
      regions: [],
      nodes: [copy],
      wires: [],
    })
    const evidence = findDeiterationEvidence(
      iterated,
      copySelection,
      10_000,
      [host.retarget],
    )
    const reversed: IdentityRetarget = {
      ...host.retarget,
      from: host.retarget.to,
      to: host.retarget.from,
    }

    expect(() => applyDeiteration(
      iterated,
      copySelection,
      evidence.justifier,
      evidence.certificate,
      [reversed],
    )).toThrowError(/copy attachment/)
  })
})

function contradictionHost() {
  const builder = new DiagramBuilder()
  const enclosingCut = builder.cut(builder.root)
  const disequalityCut = builder.cut(enclosingCut)
  const equality = builder.identity(enclosingCut, IOTA, 2)
  const disequality = builder.identity(disequalityCut, IOTA, 2)
  const survivor = builder.ref(builder.root, 'survivor', relSig([]))
  const left = builder.wire(builder.root, [
    { node: equality, port: { kind: 'identity', index: 0 } },
    { node: disequality, port: { kind: 'identity', index: 1 } },
  ])
  const right = builder.wire(builder.root, [
    { node: equality, port: { kind: 'identity', index: 1 } },
    { node: disequality, port: { kind: 'identity', index: 0 } },
  ])
  return {
    diagram: builder.build(),
    enclosingCut,
    disequalityCut,
    equality,
    disequality,
    survivor,
    left,
    right,
    evidence: { equality, disequalityCut, disequality } satisfies IdentityContradictionEvidence,
  }
}

describe('Rule 6: structural identity contradiction', () => {
  it('removes a cut containing x=y and a direct child cut containing the same unordered identity', () => {
    const host = contradictionHost()

    const discharged = applyIdentityContradiction(
      host.diagram,
      host.enclosingCut,
      host.evidence,
    )

    expect(discharged.regions[host.enclosingCut]).toBeUndefined()
    expect(discharged.regions[host.disequalityCut]).toBeUndefined()
    expect(discharged.nodes[host.equality]).toBeUndefined()
    expect(discharged.nodes[host.disequality]).toBeUndefined()
    expect(discharged.nodes[host.survivor]).toBeDefined()
    expect(discharged.wires[host.left]).toBeDefined()
    expect(discharged.wires[host.right]).toBeDefined()
  })

  it('rejects identities with mismatched signatures', () => {
    const builder = new DiagramBuilder()
    const enclosingCut = builder.cut(builder.root)
    const disequalityCut = builder.cut(enclosingCut)
    const equality = builder.identity(enclosingCut, IOTA, 2)
    const disequality = builder.identity(disequalityCut, relSig([]), 2)
    builder.wire(builder.root, [
      { node: equality, port: { kind: 'identity', index: 0 } },
    ])
    builder.wire(builder.root, [
      { node: equality, port: { kind: 'identity', index: 1 } },
    ])
    builder.wire(builder.root, [
      { node: disequality, port: { kind: 'identity', index: 0 } },
    ], relSig([]))
    builder.wire(builder.root, [
      { node: disequality, port: { kind: 'identity', index: 1 } },
    ], relSig([]))
    const diagram = builder.build()

    expect(() => applyIdentityContradiction(diagram, enclosingCut, {
      equality,
      disequalityCut,
      disequality,
    })).toThrowError(/different signatures/)
  })

  it('rejects identities with different unordered wire sets', () => {
    const builder = new DiagramBuilder()
    const enclosingCut = builder.cut(builder.root)
    const disequalityCut = builder.cut(enclosingCut)
    const equality = builder.identity(enclosingCut, IOTA, 2)
    const disequality = builder.identity(disequalityCut, IOTA, 2)
    builder.wire(builder.root, [
      { node: equality, port: { kind: 'identity', index: 0 } },
      { node: disequality, port: { kind: 'identity', index: 0 } },
    ])
    builder.wire(builder.root, [
      { node: equality, port: { kind: 'identity', index: 1 } },
    ])
    builder.wire(builder.root, [
      { node: disequality, port: { kind: 'identity', index: 1 } },
    ])
    const diagram = builder.build()

    expect(() => applyIdentityContradiction(diagram, enclosingCut, {
      equality,
      disequalityCut,
      disequality,
    })).toThrowError(/different attached wire sets/)
  })

  it('rejects a disequality cut that is not a direct child', () => {
    const builder = new DiagramBuilder()
    const enclosingCut = builder.cut(builder.root)
    const middle = builder.cut(enclosingCut)
    const disequalityCut = builder.cut(middle)
    const equality = builder.identity(enclosingCut, IOTA, 2)
    const disequality = builder.identity(disequalityCut, IOTA, 2)
    builder.wire(builder.root, [
      { node: equality, port: { kind: 'identity', index: 0 } },
      { node: disequality, port: { kind: 'identity', index: 0 } },
    ])
    builder.wire(builder.root, [
      { node: equality, port: { kind: 'identity', index: 1 } },
      { node: disequality, port: { kind: 'identity', index: 1 } },
    ])
    const diagram = builder.build()

    expect(() => applyIdentityContradiction(diagram, enclosingCut, {
      equality,
      disequalityCut,
      disequality,
    })).toThrowError(/must be a direct child/)
  })

  it('rejects non-identity node evidence and evidence outside the enclosing cut', () => {
    const host = contradictionHost()
    const nonIdentityBuilder = new DiagramBuilder()
    const enclosingCut = nonIdentityBuilder.cut(nonIdentityBuilder.root)
    const disequalityCut = nonIdentityBuilder.cut(enclosingCut)
    const equality = nonIdentityBuilder.ref(enclosingCut, 'not-equality', relSig([]))
    const disequality = nonIdentityBuilder.identity(disequalityCut, IOTA, 2)
    nonIdentityBuilder.wire(nonIdentityBuilder.root, [
      { node: disequality, port: { kind: 'identity', index: 0 } },
    ])
    nonIdentityBuilder.wire(nonIdentityBuilder.root, [
      { node: disequality, port: { kind: 'identity', index: 1 } },
    ])
    const nonIdentityDiagram = nonIdentityBuilder.build()

    expect(() => applyIdentityContradiction(nonIdentityDiagram, enclosingCut, {
      equality,
      disequalityCut,
      disequality,
    })).toThrowError(/does not name an identity node/)
    expect(() => applyIdentityContradiction(host.diagram, host.disequalityCut, host.evidence))
      .toThrowError(/directly in enclosing cut/)
  })

  it('requires an enclosing cut and exposes no old oracle contract', () => {
    const host = contradictionHost()

    expect(() => applyIdentityContradiction(host.diagram, host.diagram.root, host.evidence))
      .toThrowError(/requires a cut/)
    expect(applyIdentityContradiction.length).toBe(3)
    expect('applyInconsistentCutElim' in publicRules).toBe(false)
  })
})
