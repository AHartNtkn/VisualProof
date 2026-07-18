import { describe, expect, it } from 'vitest'
import {
  FolioDossierMotion,
  type FolioMotionClock,
} from '../../src/game/interface/folio-motion'
import { cultureId } from '../../src/game/types'
import { FakeDocument, FakeElement } from './interface-fake-dom'

class ControlledClock implements FolioMotionClock {
  readonly waits: Array<{ signal: AbortSignal; resolve: () => void }> = []

  wait(_milliseconds: number, signal: AbortSignal): Promise<void> {
    return new Promise((resolve) => this.waits.push({ signal, resolve }))
  }
}

describe('production folio dossier motion ownership', () => {
  it('lets only the latest interrupted dossier transition clear the active owner', async () => {
    const root = new FakeElement(new FakeDocument())
    const clock = new ControlledClock()
    const motion = new FolioDossierMotion(root as unknown as HTMLElement, clock)
    const first = motion.replace(cultureId('first-culture'), false)
    const second = motion.replace(cultureId('second-culture'), false)

    expect(clock.waits[0]!.signal.aborted).toBe(true)
    expect(root.dataset.motionDossierTarget).toBe('second-culture')
    expect(root.classList.contains('is-motion-dossier')).toBe(true)
    clock.waits[0]!.resolve()
    await first
    expect(root.classList.contains('is-motion-dossier')).toBe(true)
    clock.waits[1]!.resolve()
    await second
    expect(root.classList.contains('is-motion-dossier')).toBe(false)
    expect(root.dataset.motionDossierTarget).toBeUndefined()
  })

  it('settles reduced motion synchronously without creating a paused/demo mode', async () => {
    const root = new FakeElement(new FakeDocument())
    const clock = new ControlledClock()
    const motion = new FolioDossierMotion(root as unknown as HTMLElement, clock)
    await motion.replace(cultureId('first-culture'), true)
    expect(clock.waits).toHaveLength(0)
    expect(root.classList.contains('is-motion-dossier')).toBe(false)
    expect(root.dataset.motionDossierTarget).toBeUndefined()
  })

  it('gives the latest locked-selection resistance sole cleanup ownership', async () => {
    const root = new FakeElement(new FakeDocument())
    const clock = new ControlledClock()
    const motion = new FolioDossierMotion(root as unknown as HTMLElement, clock)
    const first = motion.restrictedRefusal('first-record', false)
    const second = motion.restrictedRefusal('second-record', false)

    expect(clock.waits[0]!.signal.aborted).toBe(true)
    expect(root.dataset.motionRestrictionTarget).toBe('second-record')
    expect(root.dataset.motionRestrictionKind).toBe('refuse')
    expect(root.classList.contains('is-motion-restriction')).toBe(true)
    clock.waits[0]!.resolve()
    await first
    expect(root.classList.contains('is-motion-restriction')).toBe(true)
    clock.waits[1]!.resolve()
    await second
    expect(root.classList.contains('is-motion-restriction')).toBe(false)
    expect(root.dataset.motionRestrictionTarget).toBeUndefined()
  })
})
