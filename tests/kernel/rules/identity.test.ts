import { describe, expect, it } from 'vitest'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import type { Diagram, NodeId, WireId } from '../../../src/kernel/diagram/diagram'
import { exploreForm } from '../../../src/kernel/diagram/canonical/explore'
import { derivedScope } from '../../../src/kernel/diagram/regions'
import { IOTA, relSig } from '../../../src/kernel/diagram/sig'
import { extractSubgraph } from '../../../src/kernel/diagram/subgraph/extract'
import { mkSelection } from '../../../src/kernel/diagram/subgraph/selection'
import { EMPTY_PROOF_CONTEXT, registerTheorem } from '../../../src/kernel/proof/context'
import { replayProof, type ProofStep } from '../../../src/kernel/proof/step'
import { checkTheorem, pinnedForReplay, type Theorem } from '../../../src/kernel/proof/theorem'
import { applyErasure } from '../../../src/kernel/rules/erasure'
import * as identityRules from '../../../src/kernel/rules/identity'
import * as rules from '../../../src/kernel/rules'
import { applyIdentityInsertion } from '../../../src/kernel/rules/identity'
import {
  applyIdentification,
  applyPresentation,
  applyVacuityDelete,
} from '../../../src/kernel/rules/identity-rules'
import {
  applyDeiteration,
  applyIteration,
  findDeiterationEvidence,
} from '../../../src/kernel/rules/iteration'
import { bareWire, contentEndpoints } from '../../fixtures/pins'

type IdentityNode = Extract<Diagram['nodes'][NodeId], { kind: 'identity' }>

function identityNodes(
  diagram: Diagram,
): Array<[NodeId, IdentityNode]> {
  return Object.entries(diagram.nodes)
    .filter((entry): entry is [NodeId, IdentityNode] =>
      entry[1].kind === 'identity')
}

// Construction rewrites nothing: identity nodes the author wrote survive
// build(), and each rewrite the deleted eager normalizer performed silently
// is reached here by the rule step that licenses it — or refused, where the
// eager version produced a diagram that could not be drawn.
describe('the eager identity rewrites, replayed as explicit rule steps', () => {
  it('keeps an identity looped onto one wire, whose two ends it is', () => {
    const builder = new DiagramBuilder()
    const identity = builder.identity(builder.root, IOTA, 2)
    const wire = builder.wire([
      { node: identity, port: { kind: 'identity', index: 0 } },
      { node: identity, port: { kind: 'identity', index: 1 } },
    ])
    const identityPorts = [0, 1].map((index) => ({
      node: identity,
      port: { kind: 'identity' as const, index },
    }))

    const diagram = builder.build()

    expect(diagram.nodes[identity]).toEqual({
      kind: 'identity',
      region: diagram.root,
      sig: IOTA,
      arity: 2,
    })
    expect(diagram.wires[wire]!.endpoints).toEqual(identityPorts)

    // The node asserts only x = x, so vacuity is the rule that would remove
    // it — but here it is both of the wire's ends, and a wire end is a node.
    expect(() => applyVacuityDelete(diagram, {
      nodes: { [identity]: { region: diagram.root, sig: IOTA, arity: 2 } },
      wires: {},
      attachments: { [wire]: identityPorts },
    })).toThrowError(/would leave wire '.*' with 0 end\(s\)/)
  })

  it('collapses an unconditional same-scope identity by identification', () => {
    const builder = new DiagramBuilder()
    const cut = builder.cut(builder.root)
    const identity = builder.identity(cut, IOTA, 2)
    // build() completes each wire with a pin at its sole end's region, so
    // both are quantified exactly where the identity equates them.
    const left = builder.wire([
      { node: identity, port: { kind: 'identity', index: 0 } },
    ])
    const right = builder.wire([
      { node: identity, port: { kind: 'identity', index: 1 } },
    ])

    const diagram = builder.build()

    expect(diagram.nodes[identity]).toEqual({
      kind: 'identity',
      region: cut,
      sig: IOTA,
      arity: 2,
    })
    expect(Object.keys(diagram.wires).sort()).toEqual([left, right].sort())
    expect(derivedScope(diagram, left)).toBe(cut)
    expect(derivedScope(diagram, right)).toBe(cut)

    const collapsed = applyIdentification(diagram, {
      kind: 'collapse',
      node: identity,
      survivor: left,
      absorbed: [right],
    })

    expect(Object.keys(collapsed.wires)).toEqual([left])
    // The equating port survives on the survivor, which is what keeps its
    // derived scope where it was.
    expect(collapsed.nodes[identity]).toEqual({
      kind: 'identity',
      region: cut,
      sig: IOTA,
      arity: 1,
    })
    expect(derivedScope(collapsed, left)).toBe(cut)

    const detached = applyVacuityDelete(collapsed, {
      nodes: { [identity]: { region: cut, sig: IOTA, arity: 1 } },
      wires: {},
      attachments: {
        [left]: [{ node: identity, port: { kind: 'identity', index: 0 } }],
      },
    })

    expect(detached.nodes[identity]).toBeUndefined()
    expect(Object.keys(detached.wires)).toEqual([left])
    expect(derivedScope(detached, left)).toBe(cut)
  })

  it('fuses touching same-region identities by presentation invariance', () => {
    const builder = new DiagramBuilder()
    const cut = builder.cut(builder.root)
    const first = builder.identity(cut, IOTA, 2)
    const second = builder.identity(cut, IOTA, 2)
    const outerLeft = builder.wire([
      { node: first, port: { kind: 'identity', index: 0 } },
    ])
    builder.pin(outerLeft, builder.root)
    const middle = builder.wire([
      { node: first, port: { kind: 'identity', index: 1 } },
      { node: second, port: { kind: 'identity', index: 0 } },
    ])
    builder.pin(middle, builder.root)
    const outerRight = builder.wire([
      { node: second, port: { kind: 'identity', index: 1 } },
    ])
    builder.pin(outerRight, builder.root)

    const diagram = builder.build()

    // Both authored nodes stand; the other three identities are the pins.
    expect(identityNodes(diagram)).toHaveLength(5)
    expect(diagram.nodes[first]).toMatchObject({ region: cut, arity: 2 })
    expect(diagram.nodes[second]).toMatchObject({ region: cut, arity: 2 })

    // Fusion is the port union with multiplicities: the shared wire becomes a
    // loop on the fused node rather than losing one of its two ends.
    const fused = applyPresentation(diagram, {
      region: cut,
      removeNodes: [first, second],
      addNodes: { eq: [outerLeft, middle, middle, outerRight] },
    })
    const equalities = identityNodes(fused).filter(([, node]) => node.arity > 1)

    expect(equalities).toHaveLength(1)
    expect(equalities[0]![1]).toEqual({
      kind: 'identity',
      region: cut,
      sig: IOTA,
      arity: 4,
    })
    for (const [wire, ends] of [[outerLeft, 2], [middle, 3], [outerRight, 2]] as const) {
      expect(fused.wires[wire]!.endpoints).toHaveLength(ends)
      expect(derivedScope(fused, wire)).toBe(builder.root)
    }
    expect(fused.wires[middle]!.endpoints
      .filter((endpoint) => endpoint.node === equalities[0]![0])).toHaveLength(2)
  })
})

describe('Rule 4: inherited identity insertion and ordinary erasure', () => {
  it('inserts an identity over distinct same-signature wires visible in a negative region', () => {
    const builder = new DiagramBuilder()
    const cut = builder.cut(builder.root)
    const left = bareWire(builder, builder.root)
    const right = bareWire(builder, builder.root)
    const diagram = builder.build()

    const inserted = applyIdentityInsertion(diagram, cut, [left, right])
    const identities = identityNodes(inserted).filter(([id]) =>
      diagram.nodes[id] === undefined)

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

  it('inserts an identity over co-scoped wires that identification then collapses', () => {
    const builder = new DiagramBuilder()
    const cut = builder.cut(builder.root)
    const left = bareWire(builder, cut)
    const right = bareWire(builder, cut)
    const diagram = builder.build()

    const inserted = applyIdentityInsertion(diagram, cut, [left, right])
    const identity = identityNodes(inserted)
      .find(([id]) => diagram.nodes[id] === undefined)![0]

    // Both wires are quantified exactly at the region where the insertion
    // equates them, so the one-point rule applies with no further apparatus.
    const collapsed = applyIdentification(inserted, {
      kind: 'collapse',
      node: identity,
      survivor: left,
      absorbed: [right],
    })

    expect(Object.keys(collapsed.wires)).toEqual([left])
    expect(collapsed.nodes[identity]).toEqual({
      kind: 'identity',
      region: cut,
      sig: IOTA,
      arity: 1,
    })
    // The absorbed wire's own points come across, so the survivor still ends
    // in the region the insertion named.
    expect(contentEndpoints(collapsed, left)).toEqual([])
    expect(derivedScope(collapsed, left)).toBe(cut)
  })

  it('uses the forward-negative and backward-positive polarity matrix', () => {
    const builder = new DiagramBuilder()
    const cut = builder.cut(builder.root)
    const left = bareWire(builder, builder.root)
    const right = bareWire(builder, builder.root)
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
    const visible = bareWire(builder, builder.root)
    const relation = bareWire(builder, builder.root, relSig([]))
    const hidden = bareWire(builder, child)
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
    // Both wires outlive the erased identity, so each carries the two pins
    // the floor requires at the root scope they had.
    const left = builder.wire([
      { node: identity, port: { kind: 'identity', index: 0 } },
    ])
    builder.pin(left, builder.root)
    builder.pin(left, builder.root)
    const right = builder.wire([
      { node: identity, port: { kind: 'identity', index: 1 } },
    ])
    builder.pin(right, builder.root)
    builder.pin(right, builder.root)
    const diagram = builder.build()
    const selection = mkSelection(diagram, {
      region: positive,
      regions: [],
      nodes: [identity],
      wires: [],
    })

    const erased = applyErasure(diagram, selection)

    expect(erased.nodes[identity]).toBeUndefined()
    expect(contentEndpoints(erased, left)).toEqual([])
    expect(contentEndpoints(erased, right)).toEqual([])
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
      const left = builder.wire([
        { node: identity, port: { kind: 'identity', index: swap ? 1 : 0 } },
        { node: atom, port: { kind: 'arg', index: 0 } },
      ])
      builder.pin(left, builder.root)
      const right = builder.wire([
        { node: identity, port: { kind: 'identity', index: swap ? 0 : 1 } },
      ])
      builder.pin(right, builder.root)
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

  it('derives P(b) from P(a): iterate the identity, sever, collapse, detach', () => {
    const derive = (orientation: 'forward' | 'backward') => {
      const builder = new DiagramBuilder()
      const home = builder.cut(builder.root)
      // Forward severing needs a positive site; backward a negative one.
      const site = orientation === 'forward'
        ? builder.cut(home)
        : builder.cut(builder.cut(home))
      const identity = builder.identity(home, IOTA, 2)
      const atom = builder.atom(site, relSig([IOTA]))
      builder.wire([{ node: atom, port: { kind: 'head' } }], relSig([IOTA]))
      const a = builder.wire([
        { node: identity, port: { kind: 'identity', index: 0 } },
        { node: atom, port: { kind: 'arg', index: 0 } },
      ])
      builder.pin(a, builder.root)
      const b = builder.wire([
        { node: identity, port: { kind: 'identity', index: 1 } },
      ])
      builder.pin(b, builder.root)
      const diagram = builder.build()

      const withCopy = applyIteration(diagram, mkSelection(diagram, {
        region: home,
        regions: [],
        nodes: [identity],
        wires: [],
      }), site)
      const copied = Object.keys(withCopy.nodes).find((id) =>
        diagram.nodes[id] === undefined && withCopy.nodes[id]!.kind === 'identity')!
      // Severing `a` puts the atom's argument on a fresh wire quantified at
      // the site, which is exactly where the copy equates it to `b`.
      const severed = rules.applyWireSever(withCopy, {
        wire: a,
        keep: withCopy.wires[a]!.endpoints.filter((endpoint) =>
          endpoint.node !== copied && endpoint.node !== atom),
        scope: site,
      }, orientation)
      const fresh = Object.keys(severed.wires)
        .find((id) => withCopy.wires[id] === undefined)!

      // The one-point rule lands the atom's argument on `b`.
      const collapsed = applyIdentification(severed, {
        kind: 'collapse',
        node: copied,
        survivor: b,
        absorbed: [fresh],
      })
      expect(collapsed.nodes[copied]).toMatchObject({ arity: 1 })

      // The copy is then a lone pin on a wire that already has two ends at
      // the scope it names, so vacuity detaches it.
      const substituted = applyVacuityDelete(collapsed, {
        nodes: { [copied]: { region: site, sig: IOTA, arity: 1 } },
        wires: {},
        attachments: {
          [b]: [{ node: copied, port: { kind: 'identity', index: 0 } }],
        },
      })

      const expectedBuilder = new DiagramBuilder()
      const expectedHome = expectedBuilder.cut(expectedBuilder.root)
      const expectedSite = orientation === 'forward'
        ? expectedBuilder.cut(expectedHome)
        : expectedBuilder.cut(expectedBuilder.cut(expectedHome))
      const expectedIdentity = expectedBuilder.identity(expectedHome, IOTA, 2)
      const expectedAtom = expectedBuilder.atom(expectedSite, relSig([IOTA]))
      expectedBuilder.wire([
        { node: expectedAtom, port: { kind: 'head' } },
      ], relSig([IOTA]))
      const expectedA = expectedBuilder.wire([
        { node: expectedIdentity, port: { kind: 'identity', index: 0 } },
      ])
      expectedBuilder.pin(expectedA, expectedBuilder.root)
      const expectedB = expectedBuilder.wire([
        { node: expectedIdentity, port: { kind: 'identity', index: 1 } },
        { node: expectedAtom, port: { kind: 'arg', index: 0 } },
      ])
      expectedBuilder.pin(expectedB, expectedBuilder.root)

      expect(exploreForm(substituted))
        .toBe(exploreForm(expectedBuilder.build()))
    }

    derive('forward')
    derive('backward')
  })
})

function ordinaryEqualityCutTheorem(): Theorem {
  const rhsBuilder = new DiagramBuilder()
  const enclosing = rhsBuilder.cut(rhsBuilder.root)
  const disequalityCut = rhsBuilder.cut(enclosing)
  const equality = rhsBuilder.identity(enclosing, IOTA, 2)
  const disequality = rhsBuilder.identity(disequalityCut, IOTA, 2)
  const rhsLeft = rhsBuilder.wire([
    { node: equality, port: { kind: 'identity', index: 0 } },
    { node: disequality, port: { kind: 'identity', index: 0 } },
  ])
  const rhsRight = rhsBuilder.wire([
    { node: equality, port: { kind: 'identity', index: 1 } },
    { node: disequality, port: { kind: 'identity', index: 1 } },
  ])
  const rhs = rhsBuilder.buildOpen([rhsLeft, rhsRight])
  const lhsBuilder = new DiagramBuilder()
  const left = lhsBuilder.wire([])
  const right = lhsBuilder.wire([])
  const lhs = lhsBuilder.buildOpen([left, right])
  const lhsDiagram = lhs.diagram
  // Each stated formal is a wire from its frame exit to an ∃ point. On the
  // left that point is the wire's only other end; once the equality and its
  // copy give the wire two ends inside the double cut, the point is ⊤ content
  // that vacuity removes, which is what makes the two sides the same shape.
  const point = (wire: WireId): NodeId => lhsDiagram.wires[wire]!.endpoints[0]!.node
  const dropPoint = (wire: WireId): ProofStep => ({
    rule: 'vacuity',
    direction: 'delete',
    assembly: {
      nodes: { [point(wire)]: { region: lhsDiagram.root, sig: IOTA, arity: 1 } },
      wires: {},
      attachments: {
        [wire]: [{ node: point(wire), port: { kind: 'identity', index: 0 } }],
      },
    },
  })

  return {
    name: 'ordinaryEqualityCut',
    lhs,
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
      }, dropPoint(left), dropPoint(right)],
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
    // Cite the theorem on its own right-hand side, closed the way a proof
    // replays it: each frame exit is the frame pin that makes the stated
    // wires attachments of the enclosing occurrence.
    const result = replayProof(pinnedForReplay(theorem.rhs), [{
      rule: 'theorem',
      name: theorem.name,
      at: {
        sel: { region: theorem.rhs.diagram.root, regions: [enclosing], nodes: [], wires: [] },
        args: Object.keys(theorem.rhs.diagram.wires),
      },
      direction: 'reverse',
    }], context, undefined, 'backward')

    expect(exploreForm(result, theorem.rhs.boundary))
      .toBe(exploreForm(pinnedForReplay(theorem.lhs), theorem.lhs.boundary))
  })
})
