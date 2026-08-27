import { readFileSync, writeFileSync } from 'node:fs'
import { join } from 'node:path'
import { expect } from '@wdio/globals'
import { describe, it } from 'mocha'
import {
  canvas,
  displayedPose,
  expectDoubleCut,
  expectPoseClose,
  game,
  loadSlot,
  rightClickWorld,
  storedTreeDiagram,
  type StoredDiagram,
  waitForVisibleTreeTween,
} from './native'

type Receipt = {
  readonly seedlingSlot?: string
  readonly seedlingAfter?: StoredDiagram
  readonly largeAfter?: StoredDiagram
}

const phase = process.env['GAME_E2E_PHASE'] ?? 'seedling-read'
const receiptPath = join(process.env['GAME_E2E_DATA_ROOT'] ?? '', 'double-cut.json')

function receipt(): Receipt {
  try {
    return JSON.parse(readFileSync(receiptPath, 'utf8')) as Receipt
  } catch {
    return {}
  }
}

function writeReceipt(value: Receipt): void {
  writeFileSync(receiptPath, JSON.stringify(value))
}

describe('double-cut tool use', () => {
  it('reloads the seedling move and persists a nested large-tree move from orbit', async () => {
    const saved = receipt()
    if (phase === 'seedling-read') {
      if (saved.seedlingSlot === undefined || saved.seedlingAfter === undefined) throw new Error('seedling receipt is incomplete')
      await loadSlot(saved.seedlingSlot)
      expect(storedTreeDiagram(saved.seedlingSlot, 'tree-0000')).toEqual(saved.seedlingAfter)
      return
    }

    if (phase === 'large-write') {
      await loadSlot('large-1')
      await canvas().click()
      await expect(game()).toHaveAttribute('data-camera-mode', 'orbit')
      await expect(game()).toHaveAttribute('data-orbit-target', 'tree-0000')
      const largeBefore = storedTreeDiagram('large-1', 'tree-0000')
      await canvas().moveTo({ xOffset: 8, yOffset: -16 })
      expect(largeBefore.regions['dc_5']?.kind).toBe('cut')
      const orbitPose = await displayedPose()
      await rightClickWorld()
      await waitForVisibleTreeTween()
      const largeAfter = storedTreeDiagram('large-1', 'tree-0000')
      expectDoubleCut(largeBefore, largeAfter, 'dc_5')
      await expect(game()).toHaveAttribute('data-camera-mode', 'orbit')
      await expect(game()).toHaveAttribute('data-orbit-target', 'tree-0000')
      expectPoseClose(await displayedPose(), orbitPose)
      writeReceipt({ ...saved, largeAfter })
      return
    }

    if (phase === 'large-read') {
      if (saved.largeAfter === undefined) throw new Error('large-tree receipt is incomplete')
      await loadSlot('large-1')
      expect(storedTreeDiagram('large-1', 'tree-0000')).toEqual(saved.largeAfter)
      return
    }
    throw new Error(`unknown double-cut phase '${phase}'`)
  })
})
