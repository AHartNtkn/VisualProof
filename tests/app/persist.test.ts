import { describe, expect, it } from 'vitest'
import { sessionTheory } from '../../src/app/persist'
import { registerTheorem, verifyTheory } from '../../src/kernel/proof/context'
import { loadTheory, theoryToJson } from '../../src/kernel/proof/store'
import { tinyTheory } from '../fixtures/zero-signature'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { mkDiagramWithBoundary } from '../../src/kernel/diagram/boundary'
import { singleStepAction } from '../../src/kernel/proof/action'
import { proofTermSpawnStep } from '../../src/app/interact/proof-spawn'
import { parseTerm } from '../../src/kernel/term/parse'
import { applyTrack, declareTrack, startTrack } from '../../src/app/session'
import { mkReplay } from '../../src/app/replay'

describe('session persistence', () => {
  it('round-trips structural relations and theorems without theory-specific fields', () => {
    const theory = tinyTheory()
    const ctx = verifyTheory(theory)
    const saved = sessionTheory(ctx, { relations: [...ctx.relations] })
    const loaded = loadTheory(theoryToJson(saved))
    expect([...loaded.ctx.relations.keys()]).toEqual(['UnaryWitness'])
    expect([...loaded.ctx.theorems.keys()]).toEqual(['StructuralReflexivity'])
  })

  it('round-trips a replayable Lambda spawn with all incidence caps', () => {
    const builder = new DiagramBuilder()
    const region = builder.cut(builder.root)
    const origin = mkDiagramWithBoundary(builder.build(), [])
    const base = verifyTheory(tinyTheory())
    const track = applyTrack(startTrack(origin, 'forward', base), singleStepAction(
      'Lambda expression',
      proofTermSpawnStep(parseTerm('f x'), region),
      [{ introducedNode: 0, x: 44, y: 55 }],
    ))
    const theorem = declareTrack(track, 'SpawnOpenLambda')
    const context = registerTheorem(base, theorem)

    const encoded = theoryToJson(sessionTheory(context, {
      relations: [...context.relations],
    }))
    expect(JSON.stringify(encoded)).toContain('lambdaTermSpawn')
    const loaded = loadTheory(encoded)
    const replay = mkReplay(theorem.name, loaded.ctx)
    const final = replay.diagramAt(replay.actionCount)
    const termEntry = Object.entries(final.nodes)
      .find(([, node]) => node.kind === 'term')
    if (termEntry === undefined) throw new Error('persisted replay has no term')
    const incident = Object.values(final.wires)
      .filter((wire) => wire.endpoints.some((endpoint) => endpoint.node === termEntry[0]))

    expect(termEntry[1]).toMatchObject({ kind: 'term', freeArity: 2 })
    expect(incident).toHaveLength(3)
    expect(incident.every((wire) => wire.endpoints.some((endpoint) => {
      const node = final.nodes[endpoint.node]
      return node?.kind === 'identity' && node.arity === 1
    }))).toBe(true)
  })
})
