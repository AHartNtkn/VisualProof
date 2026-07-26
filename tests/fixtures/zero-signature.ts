import { mkDiagramWithBoundary, type DiagramWithBoundary } from '../../src/kernel/diagram/boundary'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import type { Diagram } from '../../src/kernel/diagram/diagram'
import type { Theory } from '../../src/kernel/proof/context'
import { IOTA, relSig } from '../../src/kernel/diagram/sig'

export const UNARY = relSig([IOTA])
export const BINARY = relSig([IOTA, IOTA])

export function unaryDefinition(): DiagramWithBoundary {
  const builder = new DiagramBuilder()
  const atom = builder.atom(builder.root, UNARY)
  const argument = builder.wire(builder.root, [
    { node: atom, port: { kind: 'arg', index: 0 } },
  ])
  return mkDiagramWithBoundary(builder.build(), [argument])
}

export function identityInCut(): Diagram {
  const builder = new DiagramBuilder()
  const enclosing = builder.cut(builder.root)
  const negated = builder.cut(enclosing)
  const equality = builder.identity(enclosing, IOTA, 2)
  const disequality = builder.identity(negated, IOTA, 2)
  builder.wire(builder.root, [
    { node: equality, port: { kind: 'identity', index: 0 } },
    { node: disequality, port: { kind: 'identity', index: 0 } },
  ])
  builder.wire(builder.root, [
    { node: equality, port: { kind: 'identity', index: 1 } },
    { node: disequality, port: { kind: 'identity', index: 1 } },
  ])
  return builder.build()
}

export function tinyTheory(): Theory {
  const relation = unaryDefinition()
  const empty = mkDiagramWithBoundary(new DiagramBuilder().build(), [])
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
