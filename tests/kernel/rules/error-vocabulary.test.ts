import { describe, expect, it } from 'vitest'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { DiagramError } from '../../../src/kernel/diagram/diagram'
import { relSig } from '../../../src/kernel/diagram/sig'
import { mkSelection } from '../../../src/kernel/diagram/subgraph/selection'
import { applyDoubleCutElim } from '../../../src/kernel/rules/doublecut'
import { applyErasure } from '../../../src/kernel/rules/erasure'
import { RuleError } from '../../../src/kernel/rules/error'
import { applyIteration } from '../../../src/kernel/rules/iteration'
import { applyAtomSpawn } from '../../../src/kernel/rules/spawn'
import {
  applyCutWrap,
  applyEndsDelete,
  applyEndsSpawn,
  applyParallelFuse,
} from '../../../src/kernel/rules/wire-content'
import {
  applyWireJoin,
  applyWireSever,
} from '../../../src/kernel/rules/wire-quantifier'

function caughtBy(operation: () => unknown): unknown {
  try {
    operation()
  } catch (error) {
    return error
  }
  throw new Error('expected the operation to throw')
}

describe('unknown ids are DiagramError; rule-gate refusals are RuleError', () => {
  it('atom spawning with an unknown region is structural', () => {
    const builder = new DiagramBuilder()
    const cut = builder.cut(builder.root)
    const wire = builder.relWire(cut, relSig([]))
    const diagram = builder.build()

    expect(caughtBy(() => applyAtomSpawn(diagram, 'ghost', wire)))
      .toBeInstanceOf(DiagramError)
  })

  it('wire joining checks both referents before its rule gate', () => {
    const builder = new DiagramBuilder()
    const cut = builder.cut(builder.root)
    const wire = builder.wire(cut, [])
    const diagram = builder.build()

    expect(caughtBy(() => applyWireJoin(diagram, {
      kind: 'iota',
      a: 'ghost',
      b: wire,
    })))
      .toBeInstanceOf(DiagramError)
    expect(caughtBy(() => applyWireJoin(diagram, {
      kind: 'iota',
      a: wire,
      b: 'ghost',
    })))
      .toBeInstanceOf(DiagramError)
    expect(caughtBy(() => applyWireJoin(diagram, {
      kind: 'iota',
      a: 'ghost',
      b: 'ghost',
    })))
      .toBeInstanceOf(DiagramError)
  })

  it('a stale erasure selection is structural', () => {
    const builder = new DiagramBuilder()
    const cut = builder.cut(builder.root)
    const atom = builder.atom(cut, relSig([]))
    const original = builder.build()
    const selection = mkSelection(original, {
      region: cut,
      regions: [],
      nodes: [atom],
      wires: [],
    })

    expect(caughtBy(() => applyErasure(
      new DiagramBuilder().build(),
      selection,
    ))).toBeInstanceOf(DiagramError)
  })

  it('unknown sever, iteration, and double-cut ids are structural', () => {
    const empty = new DiagramBuilder().build()
    expect(caughtBy(() => applyWireSever(empty, {
      kind: 'iota',
      wire: 'ghost',
      keep: [],
    })))
      .toBeInstanceOf(DiagramError)
    expect(caughtBy(() => applyDoubleCutElim(empty, 'ghost')))
      .toBeInstanceOf(DiagramError)

    const builder = new DiagramBuilder()
    const atom = builder.atom(builder.root, relSig([]))
    const diagram = builder.build()
    const selection = mkSelection(diagram, {
      region: diagram.root,
      regions: [],
      nodes: [atom],
      wires: [],
    })
    expect(caughtBy(() => applyIteration(diagram, selection, 'ghost')))
      .toBeInstanceOf(DiagramError)
  })

  it('real referents refused by logical gates remain RuleError', () => {
    const builder = new DiagramBuilder()
    const cut = builder.cut(builder.root)
    const atom = builder.atom(cut, relSig([]))
    const relationWire = builder.relWire(builder.root, relSig([]))
    const diagram = builder.build()

    expect(caughtBy(() => applyAtomSpawn(
      diagram,
      diagram.root,
      relationWire,
    ))).toBeInstanceOf(RuleError)
    const selection = mkSelection(diagram, {
      region: cut,
      regions: [],
      nodes: [atom],
      wires: [],
    })
    expect(caughtBy(() => applyErasure(diagram, selection)))
      .toBeInstanceOf(RuleError)
  })

  it('content primitives follow the same vocabulary', () => {
    const builder = new DiagramBuilder()
    const rootWire = builder.relWire(builder.root, relSig([]))
    const diagram = builder.build()

    expect(caughtBy(() => applyCutWrap(diagram, 'ghost')))
      .toBeInstanceOf(DiagramError)
    expect(caughtBy(() => applyEndsSpawn(diagram, 'ghost', [])))
      .toBeInstanceOf(DiagramError)
    expect(caughtBy(() => applyEndsDelete(diagram, rootWire)))
      .toBeInstanceOf(RuleError)
    expect(caughtBy(() => applyParallelFuse(diagram, rootWire, rootWire)))
      .toBeInstanceOf(RuleError)
  })
})
