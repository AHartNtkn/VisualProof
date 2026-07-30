import { describe, expect, it } from 'vitest'
import { mkDiagramWithBoundary } from '../../../src/kernel/diagram/boundary'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { exploreForm } from '../../../src/kernel/diagram/canonical/explore'
import type { Diagram, WireId } from '../../../src/kernel/diagram/diagram'
import { IOTA, relSig } from '../../../src/kernel/diagram/sig'
import {
  compileRelationJoin,
  compileRelationSever,
} from '../../../src/kernel/proof/compile-content'
import {
  EMPTY_PROOF_CONTEXT,
  verifyTheory,
  type ProofContext,
} from '../../../src/kernel/proof/context'
import { applyAction } from '../../../src/kernel/proof/action'

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
  const dying = builder.wire(cut, [
    { node: atomA, port: { kind: 'head' } },
    { node: atomB, port: { kind: 'head' } },
  ], dyingSig)
  const argWires: WireId[][] = [[], []]
  dyingSig.args.forEach((argSig, index) => {
    for (const [atomAt, bucket] of [[atomA, 0], [atomB, 1]] as const) {
      bucket
      const wire = builder.wire(cut, [
        { node: atomAt, port: { kind: 'arg', index } },
      ], argSig)
      argWires[bucket]!.push(wire)
    }
  })
  const paramP = builder.relWire(builder.root, BINARY)
  const paramQ = builder.relWire(builder.root, UNARY)
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
      siteArgs[bucket]!.push(builder.wire(cut, [], argSig))
    }
  }
  const paramP = builder.relWire(builder.root, BINARY)
  const paramQ = builder.relWire(builder.root, UNARY)
  for (const bucket of [0, 1]) {
    drawSite(builder, cut, siteArgs[bucket]!, { paramP, paramQ })
  }
  return builder.build()
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
      scope: string
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
    const formal = content.wire(content.root, [
      { node: atomP, port: { kind: 'arg', index: 0 } },
    ])
    const stubP = content.wire(content.root, [
      { node: atomP, port: { kind: 'head' } },
    ], BINARY)
    const stubQ = content.wire(content.root, [
      { node: atomQ, port: { kind: 'head' } },
    ], UNARY)
    content.wire(content.root, [
      { node: atomP, port: { kind: 'arg', index: 1 } },
      { node: atomQ, port: { kind: 'arg', index: 0 } },
    ])
    const pattern = mkDiagramWithBoundary(
      content.build(),
      [formal, stubP, stubQ],
    )

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
      const y = builder.wire(cut, [])
      const siteP = builder.atom(cut, BINARY)
      attach(builder, params.paramP, siteP, { kind: 'head' })
      attach(builder, x!, siteP, { kind: 'arg', index: 0 })
      attach(builder, y, siteP, { kind: 'arg', index: 1 })
      const negation = builder.cut(cut)
      const siteQ = builder.atom(negation, UNARY)
      attach(builder, params.paramQ, siteQ, { kind: 'head' })
      attach(builder, y, siteQ, { kind: 'arg', index: 0 })
    })
    expect(exploreForm(compiled)).toEqual(exploreForm(expected))
  })

  it('compiles an applied formal', () => {
    const content = new DiagramBuilder()
    const atom = content.atom(content.root, UNARY)
    const argFormal = content.wire(content.root, [
      { node: atom, port: { kind: 'arg', index: 0 } },
    ])
    const relFormal = content.wire(content.root, [
      { node: atom, port: { kind: 'head' } },
    ], UNARY)
    const pattern = mkDiagramWithBoundary(content.build(), [argFormal, relFormal])

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
    expect(exploreForm(compiled)).toEqual(exploreForm(expected))
  })

  it('compiles negated identity content', () => {
    const content = new DiagramBuilder()
    const contentCut = content.cut(content.root)
    const eq = content.identity(contentCut, IOTA, 2)
    const left = content.wire(content.root, [
      { node: eq, port: { kind: 'identity', index: 0 } },
    ])
    const right = content.wire(content.root, [
      { node: eq, port: { kind: 'identity', index: 1 } },
    ])
    const pattern = mkDiagramWithBoundary(content.build(), [left, right])

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
    })
    expect(exploreForm(compiled)).toEqual(exploreForm(expected))
  })

  it('compiles ref content against a loaded definition', () => {
    const body = new DiagramBuilder()
    const bodyFormal = body.wire(body.root, [])
    const definition = mkDiagramWithBoundary(body.build(), [bodyFormal])
    const context = verifyTheory({
      relations: [['D', definition]],
      theorems: [],
    })

    const content = new DiagramBuilder()
    const ref = content.ref(content.root, 'D', UNARY)
    const formal = content.wire(content.root, [
      { node: ref, port: { kind: 'arg', index: 0 } },
    ])
    const pattern = mkDiagramWithBoundary(content.build(), [formal])

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
    expect(exploreForm(compiled)).toEqual(exploreForm(expected))
  })

  it('compiles empty content', () => {
    const content = new DiagramBuilder()
    const formal = content.wire(content.root, [])
    const pattern = mkDiagramWithBoundary(content.build(), [formal])

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

    const expected = expectedHost(UNARY, () => {})
    expect(exploreForm(compiled)).toEqual(exploreForm(expected))
  })

  it('compiles a relation sever as the inverse plan', () => {
    const builder = new DiagramBuilder()
    const atomA = builder.atom(builder.root, UNARY)
    const atomB = builder.atom(builder.root, UNARY)
    builder.wire(builder.root, [
      { node: atomA, port: { kind: 'head' } },
      { node: atomB, port: { kind: 'head' } },
    ], UNARY)
    const argA = builder.wire(builder.root, [
      { node: atomA, port: { kind: 'arg', index: 0 } },
    ])
    const argB = builder.wire(builder.root, [
      { node: atomB, port: { kind: 'arg', index: 0 } },
    ])
    const diagram = builder.build()

    const input = {
      scope: builder.root,
      occurrences: [
        {
          sel: { region: builder.root, regions: [], nodes: [atomA], wires: [] },
          args: [argA],
        },
        {
          sel: { region: builder.root, regions: [], nodes: [atomB], wires: [] },
          args: [argB],
        },
      ],
    } as const

    const { steps } = compileRelationSever(diagram, input, EMPTY_PROOF_CONTEXT)
    const compiled = replay(diagram, steps, EMPTY_PROOF_CONTEXT)

    // The occurrences are replaced by applications of one fresh existential
    // relation wire; the original signature wire keeps no heads.
    const expected = new DiagramBuilder()
    const expectedAtomA = expected.atom(expected.root, UNARY)
    const expectedAtomB = expected.atom(expected.root, UNARY)
    expected.wire(expected.root, [
      { node: expectedAtomA, port: { kind: 'head' } },
      { node: expectedAtomB, port: { kind: 'head' } },
    ], UNARY)
    expected.wire(expected.root, [
      { node: expectedAtomA, port: { kind: 'arg', index: 0 } },
    ])
    expected.wire(expected.root, [
      { node: expectedAtomB, port: { kind: 'arg', index: 0 } },
    ])
    expected.relWire(expected.root, UNARY)
    expect(exploreForm(compiled)).toEqual(exploreForm(expected.build()))
  })

  it('compiles repeated formals through duplication', () => {
    const content = new DiagramBuilder()
    const atom = content.atom(content.root, BINARY)
    const formal = content.wire(content.root, [
      { node: atom, port: { kind: 'arg', index: 0 } },
      { node: atom, port: { kind: 'arg', index: 1 } },
    ])
    const stubP = content.wire(content.root, [
      { node: atom, port: { kind: 'head' } },
    ], BINARY)
    const pattern = mkDiagramWithBoundary(content.build(), [formal, stubP])

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
    expect(exploreForm(compiled)).toEqual(exploreForm(expected))
  })
})
