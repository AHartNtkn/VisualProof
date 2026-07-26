import { describe, expect, it } from 'vitest'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { mkDiagramWithBoundary } from '../../../src/kernel/diagram/boundary'
import { exploreForm } from '../../../src/kernel/diagram/canonical/explore'
import { IOTA, relSig } from '../../../src/kernel/diagram/sig'
import { applyAction, type ProofAction } from '../../../src/kernel/proof/action'
import {
  EMPTY_PROOF_CONTEXT,
  registerTheorem,
  type ProofContext,
} from '../../../src/kernel/proof/context'
import { theoremFromJson, theoremToJson } from '../../../src/kernel/proof/json'
import { replayProof, type ProofStep } from '../../../src/kernel/proof/step'
import {
  applyTheorem,
  checkTheorem,
  type Theorem,
} from '../../../src/kernel/proof/theorem'
import { RuleError } from '../../../src/kernel/rules/error'

const PROPOSITION = relSig([])

function action(label: string, ...steps: ProofStep[]): ProofAction {
  return { label, steps, placements: [] }
}

function dropQ(): Theorem {
  const left = new DiagramBuilder()
  const p = left.atom(left.root, PROPOSITION)
  const q = left.atom(left.root, PROPOSITION)
  const boundary = left.wire(left.root, [
    { node: p, port: { kind: 'head' } },
    { node: q, port: { kind: 'head' } },
  ], PROPOSITION)
  const lhs = mkDiagramWithBoundary(left.build(), [boundary])

  const right = new DiagramBuilder()
  const rightP = right.atom(right.root, PROPOSITION)
  const rightBoundary = right.wire(right.root, [{
    node: rightP,
    port: { kind: 'head' },
  }], PROPOSITION)
  const rhs = mkDiagramWithBoundary(right.build(), [rightBoundary])

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
    const relationWire = builder.relWire(builder.root, PROPOSITION)
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
    const formalStub = contentBuilder.wire(contentBuilder.root, [{
      node: body,
      port: { kind: 'arg', index: 0 },
    }])
    const parameterStub = contentBuilder.wire(contentBuilder.root, [{
      node: body,
      port: { kind: 'arg', index: 1 },
    }])
    const content = mkDiagramWithBoundary(
      contentBuilder.build(),
      [formalStub, parameterStub],
    )
    const builder = new DiagramBuilder()
    const negative = builder.cut(builder.root)
    const application = builder.atom(negative, relSig([IOTA]))
    const argument = builder.wire(builder.root, [{
      node: application,
      port: { kind: 'arg', index: 0 },
    }])
    const relation = builder.wire(negative, [{
      node: application,
      port: { kind: 'head' },
    }], relSig([IOTA]))
    const parameter = builder.wire(builder.root, [])
    const lhsDiagram = builder.build()
    const grounding: ProofAction = {
      label: 'ground relation',
      steps: [{
        rule: 'wireJoin',
        input: {
          kind: 'relation',
          wire: relation,
          content,
          parameters: [parameter],
        },
      }],
      placements: [],
    }
    const rhsDiagram = applyAction(
      lhsDiagram,
      grounding,
      EMPTY_PROOF_CONTEXT,
    )
    const theorem: Theorem = {
      name: 'grounding-replay',
      lhs: mkDiagramWithBoundary(lhsDiagram, [argument, parameter]),
      rhs: mkDiagramWithBoundary(rhsDiagram, [argument, parameter]),
      actions: [grounding],
    }

    expect(() => checkTheorem(theorem, EMPTY_PROOF_CONTEXT)).not.toThrow()
  })

  it('pins ordered boundary correspondence', () => {
    const side = (swap: boolean) => {
      const builder = new DiagramBuilder()
      const unary = builder.atom(builder.root, relSig([IOTA]))
      const unaryArgument = builder.wire(builder.root, [{
        node: unary,
        port: { kind: 'arg', index: 0 },
      }])
      const binary = builder.atom(builder.root, relSig([IOTA, IOTA]))
      const binaryArgument = builder.wire(builder.root, [{
        node: binary,
        port: { kind: 'arg', index: 0 },
      }])
      return mkDiagramWithBoundary(
        builder.build(),
        swap
          ? [binaryArgument, unaryArgument]
          : [unaryArgument, binaryArgument],
      )
    }
    const lhs = side(false)
    const rhs = side(true)
    expect(exploreForm(lhs.diagram)).toBe(exploreForm(rhs.diagram))

    expect(() => checkTheorem({
      name: 'swapped',
      lhs,
      rhs,
      actions: [],
    }, EMPTY_PROOF_CONTEXT)).toThrowError(
      /does not arrive at the stated right-hand side/,
    )
  })

  it('rejects boundary arity mismatch and non-root boundaries', () => {
    const theorem = dropQ()
    expect(() => checkTheorem({
      ...theorem,
      rhs: mkDiagramWithBoundary(theorem.rhs.diagram, []),
    }, EMPTY_PROOF_CONTEXT)).toThrowError(/boundary arity mismatch/)

    const builder = new DiagramBuilder()
    const cut = builder.cut(builder.root)
    const nested = builder.wire(cut, [], IOTA)
    expect(() => mkDiagramWithBoundary(builder.build(), [nested]))
      .toThrowError(/must be scoped at the diagram root/)
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
          nodes: Object.keys(theorem.lhs.diagram.nodes),
          wires: [theorem.lhs.boundary[0]!],
        },
      })],
    }

    expect(() => checkTheorem(destroying, EMPTY_PROOF_CONTEXT))
      .toThrowError(/boundary wire .* has no semantic image/)
  })

  it('rejects a backward proof that deletes a positive goal', () => {
    const lhs = mkDiagramWithBoundary(new DiagramBuilder().build(), [])
    const rhsBuilder = new DiagramBuilder()
    const atom = rhsBuilder.atom(rhsBuilder.root, PROPOSITION)
    const wire = rhsBuilder.wire(rhsBuilder.root, [{
      node: atom,
      port: { kind: 'head' },
    }], PROPOSITION)
    const rhs = mkDiagramWithBoundary(rhsBuilder.build(), [])

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
        action('delete its empty wire', {
          rule: 'vacuousElim',
          wireId: wire,
        }),
      ],
    }, EMPTY_PROOF_CONTEXT)).toThrowError(
      /backward erasure is not supported/i,
    )
  })

  it('rejects backward identity insertion inside a negative goal region', () => {
    const side = (withIdentity: boolean) => {
      const builder = new DiagramBuilder()
      const cut = builder.cut(builder.root)
      const identity = withIdentity
        ? builder.identity(cut, IOTA, 2)
        : undefined
      const left = builder.wire(builder.root, identity === undefined
        ? []
        : [{ node: identity, port: { kind: 'identity', index: 0 } }])
      const right = builder.wire(builder.root, identity === undefined
        ? []
        : [{ node: identity, port: { kind: 'identity', index: 1 } }])
      return {
        side: mkDiagramWithBoundary(builder.build(), [left, right]),
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
    const boundary = builder.wire(builder.root, [
      { node: p, port: { kind: 'head' } },
      { node: q, port: { kind: 'head' } },
    ], PROPOSITION)
    const marker = builder.atom(builder.root, relSig([IOTA]))
    builder.wire(builder.root, [{
      node: marker,
      port: { kind: 'arg', index: 0 },
    }])
    return { diagram: builder.build(), p, q, boundary }
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

    expect(Object.values(result.nodes)).toHaveLength(2)
    expect(result.wires[host.boundary]?.endpoints).toHaveLength(1)
  })

  it('reverses at negative polarity and refuses forward use there', () => {
    const builder = new DiagramBuilder()
    const cut = builder.cut(builder.root)
    const p = builder.atom(cut, PROPOSITION)
    const boundary = builder.wire(cut, [{
      node: p,
      port: { kind: 'head' },
    }], PROPOSITION)
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
    expect(nodes).toHaveLength(2)

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
})

describe('theorem proof steps', () => {
  it('applies a registered theorem without expanding its stored proof', () => {
    const theorem = dropQ()
    const context = registerTheorem(EMPTY_PROOF_CONTEXT, theorem)
    const builder = new DiagramBuilder()
    const p = builder.atom(builder.root, PROPOSITION)
    const q = builder.atom(builder.root, PROPOSITION)
    const boundary = builder.wire(builder.root, [
      { node: p, port: { kind: 'head' } },
      { node: q, port: { kind: 'head' } },
    ], PROPOSITION)
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

    expect(Object.values(result.nodes)).toHaveLength(1)
  })
})
