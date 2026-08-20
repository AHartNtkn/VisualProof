import { describe, expect, it } from 'vitest'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { sameDiagram } from '../../../src/kernel/diagram/canonical/iso'
import type { Diagram, WireId } from '../../../src/kernel/diagram/diagram'
import { IOTA, relSig } from '../../../src/kernel/diagram/sig'
import {
  compileRelationJoin,
  compileRelationSever,
  invertStep,
} from '../../../src/kernel/proof/compile-content'
import {
  EMPTY_PROOF_CONTEXT,
  verifyTheory,
  type ProofContext,
} from '../../../src/kernel/proof/context'
import { applyAction } from '../../../src/kernel/proof/action'
import { bareWire } from '../../fixtures/pins'
import { applyWireJoin, applyWireSever } from '../../../src/kernel/rules/wire-quantifier'

const UNARY = relSig([IOTA])
const BINARY = relSig([IOTA, IOTA])

function replay(
  diagram: Diagram,
  steps: ReturnType<typeof compileRelationJoin>,
  context: ProofContext,
): Diagram {
  return applyAction(
    diagram,
    { label: 'replay', steps, placements: [] },
    context,
  )
}

/**
 * A host whose dying wire has the given signature, applied twice inside a
 * negative cut, plus sig-wire parameters P (binary) and Q (unary) at root.
 */
function host(dyingSig = UNARY) {
  const builder = new DiagramBuilder()
  const cut = builder.cut(builder.root)
  const atomA = builder.atom(cut, dyingSig)
  const atomB = builder.atom(cut, dyingSig)
  const dying = builder.wire([
    { node: atomA, port: { kind: 'head' } },
    { node: atomB, port: { kind: 'head' } },
  ], dyingSig)
  const argWires: WireId[][] = [[], []]
  dyingSig.args.forEach((argSig, index) => {
    for (const [atomAt, bucket] of [[atomA, 0], [atomB, 1]] as const) {
      bucket
      const wire = builder.wire([
        { node: atomAt, port: { kind: 'arg', index } },
      ], argSig)
      argWires[bucket]!.push(wire)
    }
  })
  const paramP = bareWire(builder, builder.root, BINARY)
  const paramQ = bareWire(builder, builder.root, UNARY)
  return { builder, cut, paramP, paramQ, dying, argWires }
}

type SiteParams = { readonly paramP: WireId; readonly paramQ: WireId }

/**
 * The expected instantiation result: the two end atoms are gone and each
 * site holds `drawSite`'s content on the site's argument wires.
 */
function expectedHost(
  dyingSig: ReturnType<typeof relSig>,
  drawSite: (
    builder: DiagramBuilder,
    cut: string,
    args: readonly WireId[],
    params: SiteParams,
  ) => void,
): Diagram {
  const builder = new DiagramBuilder()
  const cut = builder.cut(builder.root)
  const siteArgs: WireId[][] = [[], []]
  for (const bucket of [0, 1]) {
    for (const argSig of dyingSig.args) {
      siteArgs[bucket]!.push(builder.wire([], argSig))
    }
  }
  const paramP = builder.relWire(BINARY)
  const paramQ = builder.relWire(UNARY)
  for (const bucket of [0, 1]) {
    drawSite(builder, cut, siteArgs[bucket]!, { paramP, paramQ })
  }
  // Each parameter stays quantified at the root, so it carries a root pin —
  // and a second one only when no site gave it another end.
  for (const param of [paramP, paramQ]) {
    builder.pin(param, builder.root)
    if (endsOf(builder, param) < 2) builder.pin(param, builder.root)
  }
  return builder.build()
}

/** Ends a builder wire carries so far. */
function endsOf(builder: DiagramBuilder, wire: WireId): number {
  return (builder as unknown as {
    wires: Record<WireId, { endpoints: readonly unknown[] }>
  }).wires[wire]!.endpoints.length
}

/** Append an endpoint to an already-created builder wire. */
function attach(
  builder: DiagramBuilder,
  wire: WireId,
  node: string,
  port: { kind: 'head' } | { kind: 'arg'; index: number }
    | { kind: 'identity'; index: number },
): void {
  const wires = (builder as unknown as {
    wires: Record<WireId, {
      sig: unknown
      endpoints: Array<{ node: string; port: unknown }>
    }>
  }).wires
  wires[wire]!.endpoints.push({ node, port })
}

describe('compileRelationJoin against hand-built expectations', () => {
  it('compiles the worked example: ∃y.(P(x,y) ∧ ¬Q(y))', () => {
    const content = new DiagramBuilder()
    const contentCut = content.cut(content.root)
    const atomP = content.atom(content.root, BINARY)
    const atomQ = content.atom(contentCut, UNARY)
    const formal = content.wire([
      { node: atomP, port: { kind: 'arg', index: 0 } },
    ])
    const stubP = content.wire([
      { node: atomP, port: { kind: 'head' } },
    ], BINARY)
    const stubQ = content.wire([
      { node: atomQ, port: { kind: 'head' } },
    ], UNARY)
    content.wire([
      { node: atomP, port: { kind: 'arg', index: 1 } },
      { node: atomQ, port: { kind: 'arg', index: 0 } },
    ])
    const pattern = content.buildOpen([formal, stubP, stubQ])

    const fixture = host()
    const diagram = fixture.builder.build()
    const steps = compileRelationJoin(
      diagram,
      fixture.dying,
      pattern,
      [fixture.paramP, fixture.paramQ],
      EMPTY_PROOF_CONTEXT,
    )
    const compiled = replay(diagram, steps, EMPTY_PROOF_CONTEXT)

    const expected = expectedHost(UNARY, (builder, cut, [x], params) => {
      const y = builder.wire([])
      const siteP = builder.atom(cut, BINARY)
      attach(builder, params.paramP, siteP, { kind: 'head' })
      attach(builder, x!, siteP, { kind: 'arg', index: 0 })
      attach(builder, y, siteP, { kind: 'arg', index: 1 })
      const negation = builder.cut(cut)
      const siteQ = builder.atom(negation, UNARY)
      attach(builder, params.paramQ, siteQ, { kind: 'head' })
      attach(builder, y, siteQ, { kind: 'arg', index: 0 })
    })
    expect(sameDiagram(compiled, expected)).toBe(true)
  })

  it('compiles an applied formal', () => {
    const content = new DiagramBuilder()
    const atom = content.atom(content.root, UNARY)
    const argFormal = content.wire([
      { node: atom, port: { kind: 'arg', index: 0 } },
    ])
    const relFormal = content.wire([
      { node: atom, port: { kind: 'head' } },
    ], UNARY)
    const pattern = content.buildOpen([argFormal, relFormal])

    const dyingSig = relSig([IOTA, UNARY])
    const fixture = host(dyingSig)
    const diagram = fixture.builder.build()
    const steps = compileRelationJoin(
      diagram,
      fixture.dying,
      pattern,
      [],
      EMPTY_PROOF_CONTEXT,
    )
    const compiled = replay(diagram, steps, EMPTY_PROOF_CONTEXT)

    const expected = expectedHost(dyingSig, (builder, cut, [x, applied]) => {
      const site = builder.atom(cut, UNARY)
      attach(builder, applied!, site, { kind: 'head' })
      attach(builder, x!, site, { kind: 'arg', index: 0 })
    })
    expect(sameDiagram(compiled, expected)).toBe(true)
  })

  it('compiles negated identity content', () => {
    const content = new DiagramBuilder()
    const contentCut = content.cut(content.root)
    const eq = content.identity(contentCut, IOTA, 2)
    const left = content.wire([
      { node: eq, port: { kind: 'identity', index: 0 } },
    ])
    const right = content.wire([
      { node: eq, port: { kind: 'identity', index: 1 } },
    ])
    const pattern = content.buildOpen([left, right])

    const fixture = host(BINARY)
    const diagram = fixture.builder.build()
    const steps = compileRelationJoin(
      diagram,
      fixture.dying,
      pattern,
      [],
      EMPTY_PROOF_CONTEXT,
    )
    const compiled = replay(diagram, steps, EMPTY_PROOF_CONTEXT)

    const expected = expectedHost(BINARY, (builder, cut, [first, second]) => {
      const negation = builder.cut(cut)
      const eqSite = builder.identity(negation, IOTA, 2)
      attach(builder, first!, eqSite, { kind: 'identity', index: 0 })
      attach(builder, second!, eqSite, { kind: 'identity', index: 1 })
      // The equation is denied inside the negation, but both variables are
      // still quantified at the site, so each keeps its pin at the cut.
      builder.pin(first!, cut)
      builder.pin(second!, cut)
    })
    expect(sameDiagram(compiled, expected)).toBe(true)
  })

  it('compiles ref content against a loaded definition', () => {
    const body = new DiagramBuilder()
    const bodyFormal = body.wire([])
    const definition = body.buildOpen([bodyFormal])
    const context = verifyTheory({
      relations: [['D', definition]],
      theorems: [],
    })

    const content = new DiagramBuilder()
    const ref = content.ref(content.root, 'D', UNARY)
    const formal = content.wire([
      { node: ref, port: { kind: 'arg', index: 0 } },
    ])
    const pattern = content.buildOpen([formal])

    const fixture = host()
    const diagram = fixture.builder.build()
    const steps = compileRelationJoin(
      diagram,
      fixture.dying,
      pattern,
      [],
      context,
    )
    const compiled = replay(diagram, steps, context)

    const expected = expectedHost(UNARY, (builder, cut, [x]) => {
      const site = builder.ref(cut, 'D', UNARY)
      attach(builder, x!, site, { kind: 'arg', index: 0 })
    })
    expect(sameDiagram(compiled, expected)).toBe(true)
  })

  it('compiles empty content', () => {
    const content = new DiagramBuilder()
    const formal = content.wire([])
    const pattern = content.buildOpen([formal])

    const fixture = host()
    const diagram = fixture.builder.build()
    const steps = compileRelationJoin(
      diagram,
      fixture.dying,
      pattern,
      [],
      EMPTY_PROOF_CONTEXT,
    )
    const compiled = replay(diagram, steps, EMPTY_PROOF_CONTEXT)

    // ⊤ content uses no formal, so the site argument is left a bare
    // existential at the cut: a pin here, its partner minted by build().
    const expected = expectedHost(UNARY, (builder, cut, [x]) => {
      builder.pin(x!, cut)
    })
    expect(sameDiagram(compiled, expected)).toBe(true)
  })

  it('compiles a relation sever as the inverse plan', () => {
    const builder = new DiagramBuilder()
    const cut = builder.cut(builder.root)
    // Both wires are applied inside the cut but quantified at the root, so
    // each carries exactly one root pin — no more, or the compiled plan
    // would sweep the spare and stop reproducing this diagram.
    const signature = builder.relWire(UNARY)
    builder.pin(signature, builder.root)
    const shared = builder.wire([])
    builder.pin(shared, builder.root)
    const occurrence = (): string => {
      const node = builder.atom(cut, UNARY)
      attach(builder, signature, node, { kind: 'head' })
      attach(builder, shared, node, { kind: 'arg', index: 0 })
      return node
    }
    const atomA = occurrence()
    const atomB = occurrence()
    // A third occurrence stays behind: it is what keeps the signature wire
    // and the shared argument standing once the other two are abstracted.
    occurrence()
    const diagram = builder.build()

    const input = {
      scope: builder.root,
      occurrences: [
        {
          sel: { region: cut, regions: [], nodes: [atomA], wires: [] },
          args: [shared],
        },
        {
          sel: { region: cut, regions: [], nodes: [atomB], wires: [] },
          args: [shared],
        },
      ],
    } as const

    const { steps } = compileRelationSever(diagram, input, EMPTY_PROOF_CONTEXT)
    const compiled = replay(diagram, steps, EMPTY_PROOF_CONTEXT)

    // The two selected occurrences now apply one fresh existential relation
    // wire quantified at the root; the third keeps the original signature.
    const expected = new DiagramBuilder()
    const expectedCut = expected.cut(expected.root)
    const expectedSignature = expected.relWire(UNARY)
    expected.pin(expectedSignature, expected.root)
    const expectedQuantifier = expected.relWire(UNARY)
    expected.pin(expectedQuantifier, expected.root)
    const expectedShared = expected.wire([])
    expected.pin(expectedShared, expected.root)
    for (const head of [expectedSignature, expectedQuantifier, expectedQuantifier]) {
      const node = expected.atom(expectedCut, UNARY)
      attach(expected, head, node, { kind: 'head' })
      attach(expected, expectedShared, node, { kind: 'arg', index: 0 })
    }
    expect(sameDiagram(compiled, expected.build())).toBe(true)
  })

  it('compiles repeated formals through duplication', () => {
    const content = new DiagramBuilder()
    const atom = content.atom(content.root, BINARY)
    const formal = content.wire([
      { node: atom, port: { kind: 'arg', index: 0 } },
      { node: atom, port: { kind: 'arg', index: 1 } },
    ])
    const stubP = content.wire([
      { node: atom, port: { kind: 'head' } },
    ], BINARY)
    const pattern = content.buildOpen([formal, stubP])

    const fixture = host()
    const diagram = fixture.builder.build()
    const steps = compileRelationJoin(
      diagram,
      fixture.dying,
      pattern,
      [fixture.paramP],
      EMPTY_PROOF_CONTEXT,
    )
    const compiled = replay(diagram, steps, EMPTY_PROOF_CONTEXT)

    const expected = expectedHost(UNARY, (builder, cut, [x], params) => {
      const site = builder.atom(cut, BINARY)
      attach(builder, params.paramP, site, { kind: 'head' })
      attach(builder, x!, site, { kind: 'arg', index: 0 })
      attach(builder, x!, site, { kind: 'arg', index: 1 })
    })
    expect(sameDiagram(compiled, expected)).toBe(true)
  })
})

describe('invertStep for wireJoin', () => {
  /** a: P(a) inside a cut, pinned there. b: Q(b) on the sheet, pinned there. Join a into b (b is outer). */
  function joinFixture() {
    const P = relSig([IOTA])
    const bld = new DiagramBuilder()
    const cut = bld.cut(bld.root)
    const pa = bld.atom(cut, P)
    const qb = bld.atom(bld.root, P)
    const hp = bld.wire([{ node: pa, port: { kind: 'head' } }], P); bld.pin(hp, cut)
    const hq = bld.wire([{ node: qb, port: { kind: 'head' } }], P); bld.pin(hq, bld.root)
    const a = bld.wire([{ node: pa, port: { kind: 'arg', index: 0 } }]); bld.pin(a, cut)
    const b = bld.wire([{ node: qb, port: { kind: 'arg', index: 0 } }]); bld.pin(b, bld.root)
    return { pre: bld.build(), a, b }
  }

  it('severs the wire that died, at its scope, when b was the outer survivor', () => {
    const { pre, a, b } = joinFixture()
    const step = { rule: 'wireJoin', input: { a, b } } as const
    const post = applyWireJoin(pre, step.input)          // inner a (cut) dies into b (sheet)
    expect(post.wires[a]).toBeUndefined()
    const inverse = invertStep(step, pre, post)
    expect(inverse.rule).toBe('wireSever')
    if (inverse.rule !== 'wireSever') throw new Error('unreachable')
    // invertStep must identify the dying wire from which id survives in
    // `post`: here a died (scoped at the cut), so keep and scope must be
    // computed from that, not from treating b as the wire that died on the sheet.
    const restored = applyWireSever(post, inverse.input, 'backward')
    expect(sameDiagram(restored, pre, [], [])).toBe(true)
  })
})
