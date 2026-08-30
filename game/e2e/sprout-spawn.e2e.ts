import { $, expect } from '@wdio/globals'
import { Key } from 'webdriverio'
import {
  canvasScreenshot,
  createSlot,
  displayedPose,
  game,
  hold,
  rightClickWorld,
  storedTreeIds,
  waitForVisibleTreeTween,
} from './native'

async function moveFreeCameraTo(
  target: { readonly x: number; readonly y: number; readonly z: number },
): Promise<void> {
  const moveAxis = async (
    axis: 'x' | 'y' | 'z',
    positive: string,
    negative: string,
  ): Promise<void> => {
    for (let attempt = 0; attempt < 10; attempt++) {
      const delta = target[axis] - (await displayedPose()).eye[axis]
      if (Math.abs(delta) < 0.08) return
      await hold(delta > 0 ? positive : negative, Math.max(12, Math.round(Math.abs(delta) * 125)))
    }
    expect(Math.abs((await displayedPose()).eye[axis] - target[axis])).toBeLessThan(0.1)
  }
  await moveAxis('x', 'd', 'a')
  await moveAxis('z', 's', 'w')
  await moveAxis('y', Key.Space, Key.Control)
}

async function aimReticleAt(point: { readonly x: number; readonly y: number; readonly z: number }): Promise<void> {
  const { direction } = await displayedPose()
  const horizontalLength = Math.hypot(direction.x, direction.z)
  if (horizontalLength === 0) throw new Error('cannot project the reticle through a vertical view')
  const distance = 7 / horizontalLength
  await moveFreeCameraTo({
    x: point.x - direction.x * distance,
    y: point.y - direction.y * distance,
    z: point.z - direction.z * distance,
  })
}

describe('sprout spawning', () => {
  it('creates and persists a blank tree through the selected default tool', async () => {
    const slotId = await createSlot('Sprout Spawner')
    await expect(game()).toHaveAttribute('data-equipped-item', 'sprout-spawner')

    await aimReticleAt({ x: 8, y: -0.035, z: 0 })
    const before = await canvasScreenshot()
    await rightClickWorld()

    await expect($('[data-feedback]')).toHaveText(expect.stringContaining('Planted sprout tree-'))
    await waitForVisibleTreeTween(before)
    expect(storedTreeIds(slotId)).toHaveLength(2)
  })
})
