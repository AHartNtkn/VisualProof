import { describe, expect, it } from 'vitest'
import { mkDiagramWithBoundary } from '../../../src/kernel/diagram/boundary'
import type { DiagramWithBoundary } from '../../../src/kernel/diagram/boundary'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { exploreForm } from '../../../src/kernel/diagram/canonical/explore'
import type { Diagram, WireId } from '../../../src/kernel/diagram/diagram'
import { IOTA, relSig } from '../../../src/kernel/diagram/sig'
import {
  applyWireJoin,
  applyWireSever,
} from '../../../src/kernel/rules/wire-quantifier'
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
 * Extra argument positions of the dying wire attach to fresh cut-scoped
 * iota wires; a rel-sig position attaches to a shared applied wire.
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

function parity(
  diagram: Diagram,
  wire: WireId,
  content: DiagramWithBoundary,
  parameters: readonly WireId[],
  context: ProofContext = EMPTY_PROOF_CONTEXT,
): void {
  const monolith = applyWireJoin(diagram, {
    kind: 'relation',
    wire,
    content,
    parameters,
  })
  const steps = compileRelationJoin(diagram, wire, content, parameters, context)
  const compiled = replay(diagram, steps, context)
  expect(exploreForm(compiled)).toEqual(exploreForm(monolith))
}

describe('compileRelationJoin parity with the monolith', () => {
  it('compiles the worked example: ∃y.(P(x,y) ∧ ¬Q(y))', () => {
    const content = new DiagramBuilder()
    const cut = content.cut(content.root)
    const atomP = content.atom(content.root, BINARY)
    const atomQ = content.atom(cut, UNARY)
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
    parity(
      fixture.builder.build(),
      fixture.dying,
      pattern,
      [fixture.paramP, fixture.paramQ],
    )
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

    const fixture = host(relSig([IOTA, UNARY]))
    parity(fixture.builder.build(), fixture.dying, pattern, [])
  })

  it('compiles negated identity content', () => {
    const content = new DiagramBuilder()
    const cut = content.cut(content.root)
    const eq = content.identity(cut, IOTA, 2)
    const left = content.wire(content.root, [
      { node: eq, port: { kind: 'identity', index: 0 } },
    ])
    const right = content.wire(content.root, [
      { node: eq, port: { kind: 'identity', index: 1 } },
    ])
    const pattern = mkDiagramWithBoundary(content.build(), [left, right])

    const fixture = host(BINARY)
    parity(fixture.builder.build(), fixture.dying, pattern, [])
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
    const monolith = applyWireJoin(diagram, {
      kind: 'relation',
      wire: fixture.dying,
      content: pattern,
      parameters: [],
    })
    const steps = compileRelationJoin(
      diagram,
      fixture.dying,
      pattern,
      [],
      context,
    )
    expect(exploreForm(replay(diagram, steps, context)))
      .toEqual(exploreForm(monolith))
  })

  it('compiles empty content', () => {
    const content = new DiagramBuilder()
    const formal = content.wire(content.root, [])
    const pattern = mkDiagramWithBoundary(content.build(), [formal])

    const fixture = host()
    parity(fixture.builder.build(), fixture.dying, pattern, [])
  })

  it('compiles a relation sever as the inverse plan', () => {
    const builder = new DiagramBuilder()
    const atomA = builder.atom(builder.root, UNARY)
    const atomB = builder.atom(builder.root, UNARY)
    const sigWire = builder.wire(builder.root, [
      { node: atomA, port: { kind: 'head' } },
      { node: atomB, port: { kind: 'head' } },
    ], UNARY)
    void sigWire
    const argA = builder.wire(builder.root, [
      { node: atomA, port: { kind: 'arg', index: 0 } },
    ])
    const argB = builder.wire(builder.root, [
      { node: atomB, port: { kind: 'arg', index: 0 } },
    ])
    const diagram = builder.build()

    const input = {
      kind: 'relation',
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

    const monolith = applyWireSever(diagram, input)
    const { steps } = compileRelationSever(diagram, input, EMPTY_PROOF_CONTEXT)
    const compiled = replay(diagram, steps, EMPTY_PROOF_CONTEXT)
    expect(exploreForm(compiled)).toEqual(exploreForm(monolith))
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
    parity(
      fixture.builder.build(),
      fixture.dying,
      pattern,
      [fixture.paramP],
    )
  })
})
