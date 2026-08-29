import { describe, expect, it } from 'vitest'
import { emptyLibrary, loadEntry, rebuild } from '../../src/app/library'
import { sessionTheory } from '../../src/app/persist'
import { mkReplay } from '../../src/app/replay'
import { proofTermSpawnStep } from '../../src/app/interact/proof-spawn'
import { convertToNormal } from '../../src/app/tactics'
import { applyTrack, currentTrack, declareTrack, startTrack } from '../../src/app/session'
import { mkDiagramWithBoundary } from '../../src/kernel/diagram/boundary'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { singleStepAction } from '../../src/kernel/proof/action'
import { registerTheorem, verifyTheory } from '../../src/kernel/proof/context'
import { loadTheory, theoryToJson } from '../../src/kernel/proof/store'
import { parseTerm } from '../../src/kernel/term/parse'
import { tinyTheory } from '../fixtures/zero-signature'

describe('load, use, and save pipeline', () => {
  it('keeps the same structural authority through library and persistence', () => {
    const library = loadEntry(emptyLibrary(), 'tiny.json', theoryToJson(tinyTheory()))
    const boot = rebuild(library)
    const replay = mkReplay('StructuralReflexivity', boot.ctx)
    expect(replay.actionCount).toBe(0)
    const saved = sessionTheory(boot.ctx, { relations: boot.relations })
    expect([...loadTheory(theoryToJson(saved)).ctx.relations.keys()]).toEqual(['UnaryWitness'])
  })

  it('loads, rebuilds, saves, and replays a Lambda proof without changing its structural actions', () => {
    const builder = new DiagramBuilder()
    const region = builder.cut(builder.root)
    const origin = mkDiagramWithBoundary(builder.build(), [])
    const base = verifyTheory(tinyTheory())
    let track = applyTrack(startTrack(origin, 'forward', base), singleStepAction(
      'Lambda expression',
      proofTermSpawnStep(parseTerm('(\\x. x) a'), region),
      [{ introducedNode: 0, x: 80, y: 120 }],
    ))
    const term = Object.entries(currentTrack(track).nodes)
      .find(([, node]) => node.kind === 'term')
    if (term === undefined) throw new Error('Lambda pipeline fixture has no term node')
    track = applyTrack(track, singleStepAction(
      'Normalize Lambda term',
      convertToNormal(currentTrack(track), term[0], 64).step,
    ))
    const theorem = declareTrack(track, 'LambdaWorkflow')
    const context = registerTheorem(base, theorem)
    const encoded = theoryToJson(sessionTheory(context, {
      relations: [...context.relations],
    }))

    const library = loadEntry(emptyLibrary(), 'lambda.json', encoded)
    const boot = rebuild(library)
    const replay = mkReplay('LambdaWorkflow', boot.ctx)
    const saved = loadTheory(theoryToJson(sessionTheory(boot.ctx, {
      relations: boot.relations,
    })))
    const savedReplay = mkReplay('LambdaWorkflow', saved.ctx)

    expect(replay.stepsAt(1).map((step) => step.rule)).toEqual(['lambdaTermSpawn'])
    expect(replay.stepsAt(2).map((step) => step.rule)).toEqual(['lambdaConversion'])
    expect(savedReplay.actionCount).toBe(2)
    const final = savedReplay.diagramAt(2)
    const finalTerm = Object.values(final.nodes).find((node) => node.kind === 'term')
    expect(finalTerm).toMatchObject({
      kind: 'term',
      term: parseTerm('a').term,
      freeArity: 1,
    })
    expect(Object.values(final.nodes)
      .filter((node) => node.kind === 'identity' && node.arity === 1)).toHaveLength(2)
  })
})
