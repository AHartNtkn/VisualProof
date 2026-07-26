import { describe, expect, it } from 'vitest'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { mkDiagramWithBoundary } from '../../../src/kernel/diagram/boundary'
import type { Diagram, NodeId, WireId } from '../../../src/kernel/diagram/diagram'
import { exploreForm } from '../../../src/kernel/diagram/canonical/explore'
import { IOTA, relSig } from '../../../src/kernel/diagram/sig'
import { extractSubgraph } from '../../../src/kernel/diagram/subgraph/extract'
import { mkSelection, type SubgraphSelection } from '../../../src/kernel/diagram/subgraph/selection'
import { EMPTY_PROOF_CONTEXT, registerTheorem } from '../../../src/kernel/proof/context'
import { replayProof } from '../../../src/kernel/proof/step'
import { checkTheorem, type Theorem } from '../../../src/kernel/proof/theorem'
import { applyErasure } from '../../../src/kernel/rules/erasure'
import * as identityRules from '../../../src/kernel/rules/identity'
import * as rules from '../../../src/kernel/rules'
import { applyIdentityInsertion } from '../../../src/kernel/rules/identity'
import {
  applyDeiteration,
  applyIteration,
  findDeiterationEvidence,
  type IdentityRetarget,
} from '../../../src/kernel/rules/iteration'

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

  it('uses the forward-negative and backward-positive polarity matrix', () => {
    const builder = new DiagramBuilder()
    const cut = builder.cut(builder.root)
    const left = builder.wire(builder.root, [])
    const right = builder.wire(builder.root, [])
    const diagram = builder.build()

    expect(() => applyIdentityInsertion(diagram, diagram.root, [left, right]))
      .toThrowError(/identity insertion requires a negative region/)
    expect(() => applyIdentityInsertion(
      diagram,
      diagram.root,
      [left, right],
      'backward',
    )).not.toThrow()
    expect(() => applyIdentityInsertion(diagram, cut, [left, right]))
      .not.toThrow()
    expect(() => applyIdentityInsertion(
      diagram,
      cut,
      [left, right],
      'backward',
    )).toThrowError(/backward identity insertion requires a positive region/)
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
  it('round-trips an explicit conditional identity independent of incidence indices', () => {
    const roundTrip = (swap: boolean) => {
      const builder = new DiagramBuilder()
      const ancestor = builder.cut(builder.root)
      const target = builder.cut(ancestor)
      const identity = builder.identity(ancestor, IOTA, 2)
      const atom = builder.atom(ancestor, relSig([IOTA]))
      const left = builder.wire(builder.root, [
        { node: identity, port: { kind: 'identity', index: swap ? 1 : 0 } },
        { node: atom, port: { kind: 'arg', index: 0 } },
      ])
      const right = builder.wire(builder.root, [
        { node: identity, port: { kind: 'identity', index: swap ? 0 : 1 } },
      ])
      const diagram = builder.build()
      const selection = mkSelection(diagram, {
        region: ancestor,
        regions: [],
        nodes: [identity, atom],
        wires: [],
      })

      const iterated = applyIteration(diagram, selection, target)
      const copiedNodes = Object.entries(iterated.nodes)
        .filter(([id, node]) =>
          id !== identity
          && id !== atom
          && node.region === target)
        .map(([id]) => id)
      const copySelection = mkSelection(iterated, {
        region: target,
        regions: [],
        nodes: copiedNodes,
        wires: [],
      })
      const extracted = extractSubgraph(iterated, copySelection)
      expect(extracted.attachments).toContain(left)
      expect(extracted.attachments).toContain(right)

      const evidence = findDeiterationEvidence(iterated, copySelection, 10_000)
      const restored = applyDeiteration(
        iterated,
        copySelection,
        evidence.justifier,
        evidence.certificate,
      )
      return {
        source: exploreForm(diagram),
        iterated: exploreForm(iterated),
        extracted: exploreForm(
          extracted.pattern.diagram,
          extracted.pattern.boundary,
        ),
        restored: exploreForm(restored),
      }
    }

    const ordinary = roundTrip(false)
    const permuted = roundTrip(true)
    expect(ordinary.restored).toBe(ordinary.source)
    expect(permuted).toEqual(ordinary)
  })

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

function ordinaryEqualityCutTheorem(): Theorem {
  const rhsBuilder = new DiagramBuilder()
  const enclosing = rhsBuilder.cut(rhsBuilder.root)
  const disequalityCut = rhsBuilder.cut(enclosing)
  const equality = rhsBuilder.identity(enclosing, IOTA, 2)
  const disequality = rhsBuilder.identity(disequalityCut, IOTA, 2)
  const rhsLeft = rhsBuilder.wire(rhsBuilder.root, [
    { node: equality, port: { kind: 'identity', index: 0 } },
    { node: disequality, port: { kind: 'identity', index: 0 } },
  ])
  const rhsRight = rhsBuilder.wire(rhsBuilder.root, [
    { node: equality, port: { kind: 'identity', index: 1 } },
    { node: disequality, port: { kind: 'identity', index: 1 } },
  ])
  const rhs = mkDiagramWithBoundary(
    rhsBuilder.build(),
    [rhsLeft, rhsRight],
  )
  const lhsBuilder = new DiagramBuilder()
  const left = lhsBuilder.wire(lhsBuilder.root, [])
  const right = lhsBuilder.wire(lhsBuilder.root, [])
  const lhsDiagram = lhsBuilder.build()

  return {
    name: 'ordinaryEqualityCut',
    lhs: mkDiagramWithBoundary(lhsDiagram, [left, right]),
    rhs,
    actions: [{
      label: 'construct equality and its cut-contained disequality',
      placements: [],
      steps: [{
        rule: 'doubleCutIntro',
        sel: { region: lhsDiagram.root, regions: [], nodes: [], wires: [] },
      }, {
        rule: 'identityInsert', region: 'dc', wires: [left, right],
      }, {
        rule: 'iteration',
        sel: { region: 'dc', regions: [], nodes: ['identity'], wires: [] },
        target: 'dc_0',
        retargets: [],
      }],
    }],
  }
}

describe('ordinary identity contradiction theorem', () => {
  it('has no specialized identity-contradiction authority and replays by normal theorem citation', () => {
    expect(identityRules).not.toHaveProperty(['applyIdentity', 'Contradiction'].join(''))
    expect(identityRules).not.toHaveProperty(['findIdentity', 'ContradictionEvidence'].join(''))
    expect(rules).not.toHaveProperty(['applyIdentity', 'Contradiction'].join(''))

    const theorem = ordinaryEqualityCutTheorem()
    expect(() => checkTheorem(theorem, EMPTY_PROOF_CONTEXT)).not.toThrow()

    const context = registerTheorem(EMPTY_PROOF_CONTEXT, theorem)
    const enclosing = Object.entries(theorem.rhs.diagram.regions)
      .find(([, region]) => region.kind === 'cut' && region.parent === theorem.rhs.diagram.root)![0]
    const result = replayProof(theorem.rhs.diagram, [{
      rule: 'theorem',
      name: theorem.name,
      at: {
        sel: { region: theorem.rhs.diagram.root, regions: [enclosing], nodes: [], wires: [] },
        args: Object.keys(theorem.rhs.diagram.wires),
      },
      direction: 'reverse',
    }], context, undefined, 'backward')

    expect(exploreForm(result, theorem.rhs.boundary))
      .toBe(exploreForm(theorem.lhs.diagram, theorem.lhs.boundary))
  })
})
