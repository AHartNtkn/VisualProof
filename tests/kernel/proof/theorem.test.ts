import { describe, expect, it } from 'vitest'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { mkDiagramWithBoundary } from '../../../src/kernel/diagram/boundary'
import { sameDiagram } from '../../../src/kernel/diagram/canonical/iso'
import { derivedScope } from '../../../src/kernel/diagram/regions'
import { IOTA, relSig } from '../../../src/kernel/diagram/sig'
import { applyAction, type ProofAction } from '../../../src/kernel/proof/action'
import { compileRelationJoinAction } from '../../../src/kernel/proof/compile-content'
import {
  EMPTY_PROOF_CONTEXT,
  verifyTheory,
  registerTheorem,
  type ProofContext,
} from '../../../src/kernel/proof/context'
import { theoremFromJson, theoremToJson } from '../../../src/kernel/proof/json'
import { replayProof, type ProofStep } from '../../../src/kernel/proof/step'
import {
  applyTheorem,
  checkTheorem,
  pinnedForReplay,
  type Theorem,
} from '../../../src/kernel/proof/theorem'
import { RuleError } from '../../../src/kernel/rules/error'
import { bareWire } from '../../fixtures/pins'

const PROPOSITION = relSig([])

function action(label: string, ...steps: ProofStep[]): ProofAction {
  return { label, steps, placements: [] }
}

function dropQ(): Theorem {
  const left = new DiagramBuilder()
  const p = left.atom(left.root, PROPOSITION)
  const q = left.atom(left.root, PROPOSITION)
  const boundary = left.wire([
    { node: p, port: { kind: 'head' } },
    { node: q, port: { kind: 'head' } },
  ], PROPOSITION)
  const lhs = left.buildOpen([boundary])

  const right = new DiagramBuilder()
  const rightP = right.atom(right.root, PROPOSITION)
  const rightBoundary = right.wire([{
    node: rightP,
    port: { kind: 'head' },
  }], PROPOSITION)
  const rhs = right.buildOpen([rightBoundary])

  return {
    name: 'dropQ',
    lhs,
    rhs,
    actions: [action('erase Q', {
      rule: 'erasure',
      sel: {
        region: lhs.diagram.root,
        regions: [],
        nodes: [q],
        wires: [],
      },
    })],
  }
}

function introduceCapturedApplication(): Theorem {
  const builder = new DiagramBuilder()
  const relation = bareWire(builder, builder.root, relSig([IOTA]))
  const argument = bareWire(builder, builder.root)
  const lhsDiagram = builder.build()
  const lhs = mkDiagramWithBoundary(lhsDiagram, [relation, argument])

  const wrap = action('open a negative application region', {
    rule: 'doubleCutIntro',
    sel: {
      region: lhsDiagram.root,
      regions: [],
      nodes: [],
      wires: [],
    },
  })
  const wrapped = applyAction(lhsDiagram, wrap, EMPTY_PROOF_CONTEXT)
  const outer = Object.entries(wrapped.regions)
    .find(([, region]) =>
      region.kind === 'cut'
      && region.parent === wrapped.root)?.[0]
  if (outer === undefined) throw new Error('missing outer double-cut region')

  const spawn = action('apply the captured relation', {
    rule: 'atomSpawn',
    region: outer,
    wire: relation,
  })
  const spawned = applyAction(wrapped, spawn, EMPTY_PROOF_CONTEXT)
  // the spawn's own argument wire is the one the spawn pinned inside `outer`;
  // the captured `argument` stays root-scoped through its boundary pin
  const localArgument = Object.entries(spawned.wires)
    .find(([id, wire]) =>
      id !== argument
      && wire.sig.kind === 'iota'
      && derivedScope(spawned, id) === outer)?.[0]
  if (localArgument === undefined) throw new Error('missing local application argument')

  const connect = action('supply the captured argument', {
    rule: 'wireJoin',
    input: {
      a: argument,
      b: localArgument,
    },
  })
  const rhsDiagram = applyAction(spawned, connect, EMPTY_PROOF_CONTEXT)
  return {
    name: 'introduce-captured-application',
    lhs,
    rhs: mkDiagramWithBoundary(rhsDiagram, [relation, argument]),
    actions: [wrap, spawn, connect],
  }
}

function applyCertified(
  diagram: Parameters<typeof applyTheorem>[0],
  theorem: Theorem,
  at: Parameters<typeof applyTheorem>[3],
  direction: Parameters<typeof applyTheorem>[4],
  base: ProofContext = EMPTY_PROOF_CONTEXT,
) {
  const context = registerTheorem(base, theorem)
  return applyTheorem(
    diagram,
    context,
    theorem.name,
    at,
    direction,
  )
}

describe('checkTheorem', () => {
  it('accepts the exact primitive derivation and rejects an omitted proof', () => {
    const theorem = dropQ()
    expect(() => checkTheorem(theorem, EMPTY_PROOF_CONTEXT)).not.toThrow()
    expect(() => checkTheorem(
      { ...theorem, actions: [] },
      EMPTY_PROOF_CONTEXT,
    )).toThrowError(/does not arrive at the stated right-hand side/)
  })

  it('persists and honors action allocation during replay', () => {
    const builder = new DiagramBuilder()
    const cut = builder.cut(builder.root)
    const relationWire = builder.relWire(PROPOSITION)
    // a closed side supplies its own ends: the bare two-pin segment holding
    // the propositional existential at the root
    builder.pin(relationWire, builder.root)
    builder.pin(relationWire, builder.root)
    const lhsDiagram = builder.build()
    const reserved: ProofAction = {
      label: 'reserved atom',
      steps: [{
        rule: 'atomSpawn',
        region: cut,
        wire: relationWire,
      }],
      placements: [],
      allocation: {
        regions: [],
        nodes: ['n'],
        wires: [],
      },
    }
    const rhsDiagram = applyAction(
      lhsDiagram,
      reserved,
      EMPTY_PROOF_CONTEXT,
    )
    const theorem: Theorem = {
      name: 'reserved-introduction',
      lhs: mkDiagramWithBoundary(lhsDiagram, []),
      rhs: mkDiagramWithBoundary(rhsDiagram, []),
      actions: [reserved],
    }
    const loaded = theoremFromJson(
      JSON.parse(JSON.stringify(theoremToJson(theorem))),
    )

    expect(loaded.actions[0]?.allocation).toEqual(reserved.allocation)
    expect(() => checkTheorem(loaded, EMPTY_PROOF_CONTEXT)).not.toThrow()
  })

  it('replays strongest-form relation grounding while preserving theorem boundaries', () => {
    const contentBuilder = new DiagramBuilder()
    const body = contentBuilder.ref(
      contentBuilder.root,
      'G',
      relSig([IOTA, IOTA]),
    )
    const formalStub = contentBuilder.wire([{
      node: body,
      port: { kind: 'arg', index: 0 },
    }])
    const parameterStub = contentBuilder.wire([{
      node: body,
      port: { kind: 'arg', index: 1 },
    }])
    const content = contentBuilder.buildOpen([formalStub, parameterStub])
    const definitionBuilder = new DiagramBuilder()
    const definitionFormals = [
      definitionBuilder.wire([]),
      definitionBuilder.wire([]),
    ]
    const context = verifyTheory({
      relations: [['G', definitionBuilder.buildOpen(definitionFormals)]],
      theorems: [],
    })
    const builder = new DiagramBuilder()
    const negative = builder.cut(builder.root)
    const application = builder.atom(negative, relSig([IOTA]))
    const argument = builder.wire([{
      node: application,
      port: { kind: 'arg', index: 0 },
    }])
    builder.pin(argument, builder.root)
    const relation = builder.wire([{
      node: application,
      port: { kind: 'head' },
    }], relSig([IOTA]))
    const parameter = builder.wire([])
    builder.pin(parameter, builder.root)
    builder.pin(parameter, builder.root)
    // pinned at the root by its own content, so recording the grounding runs
    // on the same shape checkTheorem replays once it adds the frame pins
    const lhsDiagram = builder.build()
    const grounding: ProofAction = compileRelationJoinAction(
      'ground relation',
      lhsDiagram,
      relation,
      content,
      [parameter],
      context,
    )
    const rhsDiagram = applyAction(
      lhsDiagram,
      grounding,
      context,
    )
    const theorem: Theorem = {
      name: 'grounding-replay',
      lhs: mkDiagramWithBoundary(lhsDiagram, [argument, parameter]),
      rhs: mkDiagramWithBoundary(rhsDiagram, [argument, parameter]),
      actions: [grounding],
    }

    expect(() => checkTheorem(theorem, context)).not.toThrow()
  })

  it('pins ordered boundary correspondence', () => {
    const side = (swap: boolean) => {
      const builder = new DiagramBuilder()
      const unary = builder.atom(builder.root, relSig([IOTA]))
      const unaryArgument = builder.wire([{
        node: unary,
        port: { kind: 'arg', index: 0 },
      }])
      const binary = builder.atom(builder.root, relSig([IOTA, IOTA]))
      const binaryArgument = builder.wire([{
        node: binary,
        port: { kind: 'arg', index: 0 },
      }])
      return builder.buildOpen(
        swap
          ? [binaryArgument, unaryArgument]
          : [unaryArgument, binaryArgument],
      )
    }
    const lhs = side(false)
    const rhs = side(true)
    expect(sameDiagram(lhs.diagram, rhs.diagram)).toBe(true)

    expect(() => checkTheorem({
      name: 'swapped',
      lhs,
      rhs,
      actions: [],
    }, EMPTY_PROOF_CONTEXT)).toThrowError(
      /does not arrive at the stated right-hand side/,
    )
  })

  it('rejects boundary arity mismatch and roots every exposed wire for replay', () => {
    const theorem = dropQ()
    expect(() => checkTheorem({
      ...theorem,
      rhs: mkDiagramWithBoundary(theorem.rhs.diagram, [
        theorem.rhs.boundary[0]!,
        theorem.rhs.boundary[0]!,
      ]),
    }, EMPTY_PROOF_CONTEXT)).toThrowError(/boundary arity mismatch/)

    // A side may expose a wire all of whose endpoints sit inside a cut. The
    // frame pin replay mints for that boundary position is a root incidence,
    // which is what makes every exposed wire root-scoped during replay.
    const builder = new DiagramBuilder()
    const cut = builder.cut(builder.root)
    const inner = builder.atom(cut, relSig([IOTA]))
    const nested = builder.wire([{
      node: inner,
      port: { kind: 'arg', index: 0 },
    }])
    const side = builder.buildOpen([nested])
    expect(derivedScope(side.diagram, nested)).toBe(cut)
    expect(derivedScope(pinnedForReplay(side), nested)).toBe(side.diagram.root)
  })

  it('rejects a primitive that destroys a theorem boundary wire', () => {
    const theorem = dropQ()
    const destroying: Theorem = {
      ...theorem,
      actions: [action('destroy boundary', {
        rule: 'erasure',
        sel: {
          region: theorem.lhs.diagram.root,
          regions: [],
          // the frame pin replay mints for the single boundary entry is an
          // endpoint of that wire, so erasing the wire has to take it too
          nodes: [...Object.keys(theorem.lhs.diagram.nodes), 'framepin'],
          wires: [theorem.lhs.boundary[0]!],
        },
      })],
    }

    expect(() => checkTheorem(destroying, EMPTY_PROOF_CONTEXT))
      .toThrowError(/boundary wire .* has no semantic image/)
  })

  it('rejects a backward proof that deletes a positive goal', () => {
    const lhs = new DiagramBuilder().buildOpen([])
    const rhsBuilder = new DiagramBuilder()
    const atom = rhsBuilder.atom(rhsBuilder.root, PROPOSITION)
    const wire = rhsBuilder.wire([{
      node: atom,
      port: { kind: 'head' },
    }], PROPOSITION)
    const pin = rhsBuilder.pin(wire, rhsBuilder.root)
    const rhs = rhsBuilder.buildOpen([])

    expect(() => checkTheorem({
      name: 'fabricated-existence',
      lhs,
      rhs,
      actions: [],
      backActions: [
        action('delete the goal', {
          rule: 'erasure',
          sel: {
            region: rhs.diagram.root,
            regions: [],
            nodes: [atom],
            wires: [],
          },
        }),
        // what the erasure would leave behind: the wire held by its pin alone
        action('delete the bare remainder', {
          rule: 'vacuity',
          direction: 'delete',
          assembly: {
            nodes: {
              [pin]: { region: rhs.diagram.root, sig: PROPOSITION, arity: 1 },
            },
            wires: {
              [wire]: {
                sig: PROPOSITION,
                endpoints: [{ node: pin, port: { kind: 'identity', index: 0 } }],
              },
            },
            attachments: {},
          },
        }),
      ],
    }, EMPTY_PROOF_CONTEXT)).toThrowError(
      /backward erasure requires a negative region/i,
    )
  })

  it('rejects backward identity insertion inside a negative goal region', () => {
    const side = (withIdentity: boolean) => {
      const builder = new DiagramBuilder()
      const cut = builder.cut(builder.root)
      const identity = withIdentity
        ? builder.identity(cut, IOTA, 2)
        : undefined
      const left = builder.wire(identity === undefined
        ? []
        : [{ node: identity, port: { kind: 'identity', index: 0 } }])
      const right = builder.wire(identity === undefined
        ? []
        : [{ node: identity, port: { kind: 'identity', index: 1 } }])
      return {
        side: builder.buildOpen([left, right]),
        cut,
        left,
        right,
      }
    }
    const lhs = side(true)
    const rhs = side(false)

    expect(() => checkTheorem({
      name: 'fabricated-negative-identity',
      lhs: lhs.side,
      rhs: rhs.side,
      actions: [],
      backActions: [action('insert equality backward', {
        rule: 'identityInsert',
        region: rhs.cut,
        wires: [rhs.left, rhs.right],
      })],
    }, EMPTY_PROOF_CONTEXT)).toThrowError(
      /backward identity insertion requires a positive region/i,
    )
  })
})

describe('applyTheorem', () => {
  function positiveHost() {
    const builder = new DiagramBuilder()
    const p = builder.atom(builder.root, PROPOSITION)
    const q = builder.atom(builder.root, PROPOSITION)
    const boundary = builder.wire([
      { node: p, port: { kind: 'head' } },
      { node: q, port: { kind: 'head' } },
    ], PROPOSITION)
    // the theorem exposes this wire at the root, and the host has to supply
    // that end itself: the rewrite leaves P's head as its only other end
    const hold = builder.pin(boundary, builder.root)
    const marker = builder.atom(builder.root, relSig([IOTA]))
    builder.wire([{
      node: marker,
      port: { kind: 'arg', index: 0 },
    }])
    return { diagram: builder.build(), p, q, boundary, hold }
  }

  it('rewrites an exact positive occurrence in one native step', () => {
    const host = positiveHost()
    const result = applyCertified(
      host.diagram,
      dropQ(),
      {
        sel: {
          region: host.diagram.root,
          regions: [],
          nodes: [host.p, host.q],
          wires: [],
        },
        args: [host.boundary],
      },
      'forward',
    )

    // Q is gone; P and the marker are the only atoms left. The other three
    // nodes are pins: the one holding the cited wire and one completing each
    // of the marker's two ports.
    expect(Object.values(result.nodes).filter((node) => node.kind === 'atom'))
      .toHaveLength(2)
    expect(Object.values(result.nodes)).toHaveLength(5)
    expect(result.wires[host.boundary]?.endpoints).toEqual([
      { node: host.hold, port: { kind: 'identity', index: 0 } },
      expect.objectContaining({ port: { kind: 'head' } }),
    ])
  })

  it('reverses at negative polarity and refuses forward use there', () => {
    const builder = new DiagramBuilder()
    const cut = builder.cut(builder.root)
    const p = builder.atom(cut, PROPOSITION)
    const boundary = builder.wire([{
      node: p,
      port: { kind: 'head' },
    }], PROPOSITION)
    // the quantifier of the cited wire lives in the cut, held there by the
    // pin build() completes it with
    const diagram = builder.build()
    const strengthened = applyCertified(
      diagram,
      dropQ(),
      {
        sel: {
          region: cut,
          regions: [],
          nodes: [p],
          wires: [],
        },
        args: [boundary],
      },
      'reverse',
    )
    const nodes = Object.keys(strengthened.nodes)
    // the two atoms of the strengthened side, plus the pin already holding
    // the cited wire's quantifier in the cut
    expect(Object.values(strengthened.nodes).filter((node) => node.kind === 'atom'))
      .toHaveLength(2)
    expect(nodes).toHaveLength(3)

    expect(() => applyCertified(
      strengthened,
      dropQ(),
      {
        sel: {
          region: cut,
          regions: [],
          nodes,
          wires: [],
        },
        args: [boundary],
      },
      'forward',
    )).toThrowError(/requires a positive region/)
  })

  it('refuses mismatched occurrences and wrong polarity by name', () => {
    const host = positiveHost()
    expect(() => applyCertified(
      host.diagram,
      dropQ(),
      {
        sel: {
          region: host.diagram.root,
          regions: [],
          nodes: [host.p],
          wires: [],
        },
        args: [host.boundary],
      },
      'forward',
    )).toThrowError(/not an occurrence of theorem 'dropQ'/)

    let caught: unknown
    try {
      applyCertified(
        host.diagram,
        dropQ(),
        {
          sel: {
            region: host.diagram.root,
            regions: [],
            nodes: [host.p, host.q],
            wires: [],
          },
          args: [host.boundary],
        },
        'reverse',
      )
    } catch (error) {
      caught = error
    }
    expect(caught).toBeInstanceOf(RuleError)
    expect((caught as Error).message)
      .toMatch(/reverse requires a negative region/)
  })

  it('cites a capture-only theorem side using ordered host arguments', () => {
    const theorem = introduceCapturedApplication()
    expect(() => checkTheorem(theorem, EMPTY_PROOF_CONTEXT)).not.toThrow()

    const host = new DiagramBuilder()
    const relation = bareWire(host, host.root, relSig([IOTA]))
    const argument = bareWire(host, host.root)
    const diagram = host.build()
    const result = applyCertified(
      diagram,
      theorem,
      {
        sel: {
          region: diagram.root,
          regions: [],
          nodes: [],
          wires: [],
        },
        args: [relation, argument],
      },
      'forward',
    )

    const application = Object.values(result.nodes)
      .find((node) => node.kind === 'atom')
    expect(application?.kind).toBe('atom')
    expect(result.wires[relation]?.endpoints)
      .toContainEqual(expect.objectContaining({ port: { kind: 'head' } }))
    expect(result.wires[argument]?.endpoints)
      .toContainEqual(expect.objectContaining({ port: { kind: 'arg', index: 0 } }))
  })

  it('refuses invalid capture-only theorem arguments without diagonalizing', () => {
    const theorem = introduceCapturedApplication()
    const host = new DiagramBuilder()
    const relation = bareWire(host, host.root, relSig([IOTA]))
    const argument = bareWire(host, host.root)
    const otherArgument = bareWire(host, host.root)
    const diagram = host.build()
    const emptySelection = {
      region: diagram.root,
      regions: [],
      nodes: [],
      wires: [],
    } as const

    expect(() => applyCertified(
      diagram,
      theorem,
      { sel: emptySelection, args: [relation] },
      'forward',
    )).toThrowError(/2 boundary positions but 1 arguments/)

    // position 0 captures the relation and position 1 the individual, so
    // swapping them gives the capture stubs the wrong sorts
    expect(() => applyCertified(
      diagram,
      theorem,
      { sel: emptySelection, args: [argument, relation] },
      'forward',
    )).toThrowError(/sig 'i' does not match port 'i:0' of node '.*' expecting '\(i\)'/)

    const aliases = new DiagramBuilder()
    const first = bareWire(aliases, aliases.root)
    const second = bareWire(aliases, aliases.root)
    const aliasSide = mkDiagramWithBoundary(aliases.build(), [first, second])
    const aliasTheorem: Theorem = {
      name: 'distinct-captures',
      lhs: aliasSide,
      rhs: aliasSide,
      actions: [],
    }
    expect(() => applyCertified(
      diagram,
      aliasTheorem,
      { sel: emptySelection, args: [argument, argument] },
      'forward',
    )).toThrowError(/not an occurrence/)

    const repeated = new DiagramBuilder()
    const repeatedCapture = bareWire(repeated, repeated.root)
    const repeatedSide = mkDiagramWithBoundary(
      repeated.build(),
      [repeatedCapture, repeatedCapture],
    )
    const repeatedTheorem: Theorem = {
      name: 'repeated-capture',
      lhs: repeatedSide,
      rhs: repeatedSide,
      actions: [],
    }
    expect(() => applyCertified(
      diagram,
      repeatedTheorem,
      { sel: emptySelection, args: [argument, otherArgument] },
      'forward',
    )).toThrowError(/not an occurrence/)
  })

  it('refuses capture arguments whose scope does not enclose the application region', () => {
    const theorem = introduceCapturedApplication()
    const host = new DiagramBuilder()
    const left = host.cut(host.root)
    const outer = host.cut(host.root)
    const right = host.cut(outer)
    // the relation's quantifier lives in `left`, which is not an ancestor of
    // the `right` region the citation would splice into
    const relation = bareWire(host, left, relSig([IOTA]))
    const argument = bareWire(host, host.root)
    const diagram = host.build()

    expect(() => applyCertified(
      diagram,
      theorem,
      {
        sel: {
          region: right,
          regions: [],
          nodes: [],
          wires: [],
        },
        args: [relation, argument],
      },
      'forward',
    )).toThrowError(/does not enclose splice region/)
  })
})

describe('theorem proof steps', () => {
  it('applies a registered theorem without expanding its stored proof', () => {
    const theorem = dropQ()
    const context = registerTheorem(EMPTY_PROOF_CONTEXT, theorem)
    const builder = new DiagramBuilder()
    const p = builder.atom(builder.root, PROPOSITION)
    const q = builder.atom(builder.root, PROPOSITION)
    const boundary = builder.wire([
      { node: p, port: { kind: 'head' } },
      { node: q, port: { kind: 'head' } },
    ], PROPOSITION)
    // the host end standing for the theorem's boundary position
    builder.pin(boundary, builder.root)
    const diagram = builder.build()

    const result = replayProof(diagram, [{
      rule: 'theorem',
      name: 'dropQ',
      at: {
        sel: {
          region: diagram.root,
          regions: [],
          nodes: [p, q],
          wires: [],
        },
        args: [boundary],
      },
      direction: 'forward',
    }], context)

    // P alone, still held on the cited wire by the host's pin
    expect(Object.values(result.nodes).filter((node) => node.kind === 'atom'))
      .toHaveLength(1)
    expect(Object.values(result.nodes)).toHaveLength(2)
  })
})
