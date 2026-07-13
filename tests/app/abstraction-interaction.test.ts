import { describe, expect, it } from 'vitest'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { mkSelection } from '../../src/kernel/diagram/subgraph/selection'
import type { ProofAction } from '../../src/kernel/proof/action'
import { mkEngine } from '../../src/view/engine'
import { LIGHT } from '../../src/view/paint'
import { AbstractTransaction } from '../../src/app/relation-transactions'
import { currentRelationDraft } from '../../src/app/relation-workspace-draft'

describe('provisional abstraction interaction', () => {
  for (const configured of [
    { orientation: 'forward' as const, nested: false },
    { orientation: 'backward' as const, nested: true },
  ]) {
    it(`keeps the ${configured.orientation} source/cursor/actions untouched until one normal finalization`, () => {
      const builder = new DiagramBuilder()
      const anchor = configured.nested ? builder.cut(builder.root) : builder.root
      const diagram = builder.build()
      const wrap = mkSelection(diagram, { region: anchor, regions: [], nodes: [], wires: [] })
      const actions: ProofAction[] = []
      let cancelled = 0
      const transaction = new AbstractTransaction({
        diagram: () => diagram,
        boundary: () => [],
        wrap,
        context: () => ({ theorems: new Map(), relations: new Map() }),
        orientation: configured.orientation,
        apply: (action) => { actions.push(action) },
        cancel: () => { cancelled++ },
        engine: () => mkEngine(diagram, []),
        theme: () => LIGHT,
        matcherFuel: () => 64,
        solverFuel: () => 1024,
      })
      const draft = transaction.initialDraft()
      const sourceBefore = JSON.stringify(diagram)

      transaction.draftChanged(currentRelationDraft(draft))
      expect(JSON.stringify(diagram)).toBe(sourceBefore)
      expect(draft.cursor).toBe(0)
      expect(actions).toEqual([])
      expect(transaction.previewShapes().some((shape) => shape.kind === 'circle')).toBe(true)
      transaction.cancel()
      expect(cancelled).toBe(1)
      expect(JSON.stringify(diagram)).toBe(sourceBefore)
      expect(actions).toEqual([])

      transaction.finalize(currentRelationDraft(draft), [])
      expect(actions).toHaveLength(1)
      expect(actions[0]).toMatchObject({
        label: 'abstract relation',
        steps: [{ rule: 'comprehensionAbstract', wrap }],
      })
    })
  }
})
