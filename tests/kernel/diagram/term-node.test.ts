import { describe, expect, it } from 'vitest'
import {
  mkDiagram,
  requiredPorts,
  type Diagram,
  type NodeId,
} from '../../../src/kernel/diagram/diagram'
import { spawnTermNode } from '../../../src/kernel/diagram/spawn'
import { IOTA } from '../../../src/kernel/diagram/sig'
import { parseTerm } from '../../../src/kernel/term/parse'
import type { Term } from '../../../src/kernel/term/term'

function termNodeFixture(term: Term, interfaceArity: number): {
  readonly diagram: Diagram
  readonly node: NodeId
  readonly portSignatures: readonly unknown[]
} {
  const empty = mkDiagram({ root: 'r0', regions: { r0: { kind: 'sheet' } } })
  const built = spawnTermNode(empty, empty.root, term, interfaceArity)
  return {
    diagram: built.diagram,
    node: built.node,
    portSignatures: built.wires.map((wire) => built.diagram.wires[wire]!.sig),
  }
}

describe('term diagram nodes', () => {
  it('requires one IOTA output and one IOTA port per numeric free slot', () => {
    const term = parseTerm('\\x. x y').term
    const built = termNodeFixture(term, 1)
    expect(requiredPorts(built.diagram.nodes[built.node]!)).toEqual([
      { kind: 'output' },
      { kind: 'free', index: 0 },
    ])
    expect(built.portSignatures).toEqual([IOTA, IOTA])
  })
})
