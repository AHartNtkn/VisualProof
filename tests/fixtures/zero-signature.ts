import type { DiagramWithBoundary } from '../../src/kernel/diagram/boundary'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import type { Diagram } from '../../src/kernel/diagram/diagram'
import type { Theory } from '../../src/kernel/proof/context'
import { IOTA, relSig } from '../../src/kernel/diagram/sig'

export const UNARY = relSig([IOTA])
export const BINARY = relSig([IOTA, IOTA])

export function unaryDefinition(): DiagramWithBoundary {
  const builder = new DiagramBuilder()
  const atom = builder.atom(builder.root, UNARY)
  const argument = builder.wire([
    { node: atom, port: { kind: 'arg', index: 0 } },
  ])
  return builder.buildOpen([argument])
}

export function identityInCut(): Diagram {
  const builder = new DiagramBuilder()
  const enclosing = builder.cut(builder.root)
  const negated = builder.cut(enclosing)
  const equality = builder.identity(enclosing, IOTA, 2)
  const disequality = builder.identity(negated, IOTA, 2)
  builder.wire([
    { node: equality, port: { kind: 'identity', index: 0 } },
    { node: disequality, port: { kind: 'identity', index: 0 } },
  ])
  builder.wire([
    { node: equality, port: { kind: 'identity', index: 1 } },
    { node: disequality, port: { kind: 'identity', index: 1 } },
  ])
  return builder.build()
}

/** A retained high-valence identity connected to named unary refs across a cut.
 * The inherited root-scoped wires make the identity conditional, so canonical
 * normalization preserves it for view and physics fixtures. */
export function identityRefScene(): Diagram {
  const builder = new DiagramBuilder()
  const cut = builder.cut(builder.root)
  const identity = builder.identity(cut, IOTA, 4)
  for (let index = 0; index < 4; index++) {
    const ref = builder.ref(builder.root, `R${index}`, UNARY)
    builder.wire([
      { node: ref, port: { kind: 'arg', index: 0 } },
      { node: identity, port: { kind: 'identity', index } },
    ])
  }
  return builder.build()
}

/** A deterministic scene with both a high-degree wire junction and a retained
 * high-valence identity. It replaces theory-replay snapshots in physics tests. */
export function identityJunctionScene(): Diagram {
  const builder = new DiagramBuilder()
  const cut = builder.cut(builder.root)
  const identity = builder.identity(cut, IOTA, 4)
  const refs = Array.from(
    { length: 6 },
    (_, index) => builder.ref(builder.root, `J${index}`, UNARY),
  )
  builder.wire([
    ...refs.slice(0, 3).map((node) => ({
      node,
      port: { kind: 'arg' as const, index: 0 },
    })),
    { node: identity, port: { kind: 'identity', index: 0 } },
  ])
  for (let index = 1; index < 4; index++) {
    builder.wire([
      { node: refs[index + 2]!, port: { kind: 'arg', index: 0 } },
      { node: identity, port: { kind: 'identity', index } },
    ])
  }
  return builder.build()
}

/** A deterministic scene whose settled rest holds a junction in a genuine
 * barrier-separated basin: two 3-terminal wires must route their Steiner
 * junctions around a bulky cut (six refs inside), so a better junction basin
 * lies across the cut-circle obstacle. Point-node identities are wire
 * terminals, not obstacles, so the cusp comes from drawn discs alone. */
export function junctionCuspScene(): Diagram {
  const builder = new DiagramBuilder()
  const cut = builder.cut(builder.root)
  for (let index = 0; index < 6; index++) builder.ref(cut, `C${index}`, UNARY)
  for (let wire = 0; wire < 2; wire++) {
    const refs = Array.from(
      { length: 3 },
      (_, index) => builder.ref(builder.root, `W${wire}P${index}`, UNARY),
    )
    builder.wire(refs.map((node) => ({ node, port: { kind: 'arg' as const, index: 0 } })))
  }
  return builder.build()
}

export function commutedBoundaryRefs(): {
  readonly lhs: DiagramWithBoundary
  readonly rhs: DiagramWithBoundary
} {
  const ternary = relSig([IOTA, IOTA, IOTA])
  const side = (argumentAtBoundary: readonly number[]): DiagramWithBoundary => {
    const builder = new DiagramBuilder()
    const ref = builder.ref(builder.root, 'Ternary', ternary)
    const boundary = argumentAtBoundary.map((index) =>
      builder.wire([
        { node: ref, port: { kind: 'arg', index } },
      ]))
    return builder.buildOpen(boundary)
  }
  return {
    lhs: side([1, 0, 2]),
    rhs: side([0, 1, 2]),
  }
}

export function tinyTheory(): Theory {
  const relation = unaryDefinition()
  const empty = new DiagramBuilder().buildOpen([])
  return {
    relations: [['UnaryWitness', relation]],
    theorems: [{
      name: 'StructuralReflexivity',
      lhs: empty,
      rhs: empty,
      actions: [],
    }],
  }
}
