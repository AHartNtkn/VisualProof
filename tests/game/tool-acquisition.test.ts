import { describe, expect, it } from 'vitest'
import { acquireToolForLedger } from '../../game/tool-acquisition'
import { ToolInventory } from '../../src/game/tools'
import {
  decodeToolContent,
  LiveToolContent,
  openingToolContent,
} from '../../src/game/tools/content'

describe('ledger tool acquisition boundary', () => {
  it('reports the current live authored name after acquiring by immutable ID', () => {
    // Catches main-path acquisition feedback retaining mechanics or pre-publication copy.
    const live = new LiveToolContent(decodeToolContent(
      openingToolContent.current.definitions.map((definition) => ({
        ...definition,
        name: `Initial ${definition.id}`,
        description: `Initial description for ${definition.id}.`,
      })),
    ))
    const inventory = new ToolInventory(new Set(['sprout-spawner']))
    live.publish(decodeToolContent(live.current.definitions.map((definition) => ({
      ...definition,
      name: definition.id === 'double-cut' ? 'Saved live cutter name' : definition.name,
    }))))

    const feedback = acquireToolForLedger({
      toolId: 'double-cut',
      tools: inventory,
      reputation: 0,
      currentContent: () => live.current,
    })

    expect(inventory.snapshotForSave()).toEqual(['sprout-spawner', 'double-cut'])
    expect(feedback).toBe('Acquired Saved live cutter name.')
  })
})
