import type { ToolId, ToolInventory } from '../src/game/tools'
import type { ToolContentRevision } from '../src/game/tools/content'

export type LedgerToolAcquisition = {
  readonly toolId: ToolId
  readonly tools: ToolInventory
  readonly reputation: number
  readonly currentContent: () => ToolContentRevision
}

export function acquireToolForLedger(acquisition: LedgerToolAcquisition): string {
  acquisition.tools.acquire(acquisition.toolId, acquisition.reputation)
  return `Acquired ${acquisition.currentContent().definition(acquisition.toolId).name}.`
}
