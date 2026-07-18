import { createHash } from 'node:crypto'
import { readFileSync } from 'node:fs'
import { describe, expect, expectTypeOf, it } from 'vitest'
import {
  FolioMotion,
  type FolioMotionClock,
} from '../../src/game/interface/folio-motion'
import { cultureId, puzzleId } from '../../src/game/types'
import { FakeDocument, FakeElement } from './interface-fake-dom'

type PendingWait = {
  milliseconds: number
  resolve: () => void
  signal: AbortSignal
}

class ControlledClock implements FolioMotionClock {
  readonly waits: PendingWait[] = []

  wait(milliseconds: number, signal: AbortSignal): Promise<void> {
    return new Promise((resolve) => {
      const wait = { milliseconds, resolve, signal }
      this.waits.push(wait)
      signal.addEventListener('abort', () => {
        const index = this.waits.indexOf(wait)
        if (index >= 0) this.waits.splice(index, 1)
        resolve()
      }, { once: true })
    })
  }

  tick(): void {
    this.waits.shift()?.resolve()
  }
}

type PaintedStyle = Pick<CSSStyleDeclaration, 'transform' | 'boxShadow' | 'filter'>

class MotionDocument extends FakeDocument {
  private readonly painted = new WeakMap<object, PaintedStyle>()
  readonly defaultView = {
    getComputedStyle: (element: object): PaintedStyle => this.painted.get(element) ?? {
      transform: 'none',
      boxShadow: 'none',
      filter: 'none',
    },
  }

  paint(element: FakeElement, style: PaintedStyle): void {
    this.painted.set(element, style)
  }
}

const fixture = (): {
  root: FakeElement
  cover: FakeElement
  record: FakeElement
  document: MotionDocument
  clock: ControlledClock
  motion: FolioMotion
} => {
  const document = new MotionDocument()
  const root = new FakeElement(document)
  const cover = new FakeElement(document)
  const record = new FakeElement(document)
  cover.classList.add('cover-surface')
  record.classList.add('inspection-record')
  root.append(cover, record)
  const clock = new ControlledClock()
  return {
    root,
    cover,
    record,
    document,
    clock,
    motion: new FolioMotion(root as unknown as HTMLElement, clock),
  }
}

const descriptorCases = [
  {
    label: 'cover opening', channel: 'cover', target: 'open', kind: 'open', duration: 380,
    begin: (motion: FolioMotion) => motion.cover('open', false),
  },
  {
    label: 'cover closing', channel: 'cover', target: 'closed', kind: 'close', duration: 380,
    begin: (motion: FolioMotion) => motion.cover('closed', false),
  },
  {
    label: 'dossier replacement', channel: 'dossier', target: 'seyric', kind: 'replace', duration: 260,
    begin: (motion: FolioMotion) => motion.dossier(cultureId('seyric'), false),
  },
  {
    label: 'record inspection', channel: 'record', target: 'ossuary-seal', kind: 'inspect', duration: 340,
    begin: (motion: FolioMotion) => motion.recordInspection(puzzleId('ossuary-seal'), true, false),
  },
  {
    label: 'record return', channel: 'record', target: 'ossuary-seal', kind: 'return', duration: 340,
    begin: (motion: FolioMotion) => motion.recordInspection(puzzleId('ossuary-seal'), false, false),
  },
  {
    label: 'restricted refusal', channel: 'restriction', target: 'chamber-seal', kind: 'refuse', duration: 320,
    begin: (motion: FolioMotion) => motion.restrictedRefusal(puzzleId('chamber-seal'), false),
  },
  {
    label: 'packet release', channel: 'packet', target: 'myratic', kind: 'release', duration: 480,
    begin: (motion: FolioMotion) => motion.packetRelease(false),
  },
] as const

const key = (channel: string, suffix: string): string =>
  `motion${channel[0]!.toUpperCase()}${channel.slice(1)}${suffix}`

describe('production folio motion coordinator', () => {
  it.each(descriptorCases)(
    'owns the exact full-motion descriptor for $label',
    async ({ channel, target, kind, duration, begin }) => {
      const { root, clock, motion } = fixture()

      const complete = begin(motion)

      expect(clock.waits).toHaveLength(1)
      expect(clock.waits[0]!.milliseconds).toBe(duration)
      expect(root.classList.contains(`is-motion-${channel}`)).toBe(true)
      expect(root.dataset[key(channel, 'Target')]).toBe(target)
      expect(root.dataset[key(channel, 'Kind')]).toBe(kind)
      expect(root.style.getPropertyValue(`--motion-${channel}-duration`)).toBe(`${duration}ms`)
      expect(Object.keys(root.dataset).some((name) => name.endsWith('Phase'))).toBe(false)

      clock.tick()
      await complete

      expect(root.classList.contains(`is-motion-${channel}`)).toBe(false)
      expect(root.dataset[key(channel, 'Target')]).toBeUndefined()
      expect(root.dataset[key(channel, 'Kind')]).toBeUndefined()
      expect(root.style.getPropertyValue(`--motion-${channel}-duration`)).toBe('')
    },
  )

  it.each(descriptorCases.filter(({ label }) => !label.includes('closing') && !label.includes('return')))(
    'substitutes one 90ms reduced-depth timeline for $label',
    async ({ channel, target }) => {
      const { root, clock, motion } = fixture()
      const complete = channel === 'record'
        ? motion.recordInspection(puzzleId(target), true, true)
        : channel === 'restriction'
          ? motion.restrictedRefusal(puzzleId(target), true)
          : channel === 'dossier'
            ? motion.dossier(cultureId(target), true)
            : channel === 'cover'
              ? motion.cover('open', true)
              : motion.packetRelease(true)

      expect(clock.waits).toHaveLength(1)
      expect(clock.waits[0]!.milliseconds).toBe(90)
      expect(root.dataset[key(channel, 'Target')]).toBe(target)
      expect(root.dataset[key(channel, 'Kind')]).toBe('reduced')
      expect(root.style.getPropertyValue(`--motion-${channel}-duration`)).toBe('90ms')

      clock.tick()
      await complete
    },
  )

  it('exposes only the production reduced-motion boolean, with no paused mode', () => {
    expectTypeOf<FolioMotion['cover']>().parameter(1).toEqualTypeOf<boolean>()
    expectTypeOf<FolioMotion['dossier']>().parameter(1).toEqualTypeOf<boolean>()
    expectTypeOf<FolioMotion['recordInspection']>().parameter(2).toEqualTypeOf<boolean>()
    expectTypeOf<FolioMotion['restrictedRefusal']>().parameter(1).toEqualTypeOf<boolean>()
    expectTypeOf<FolioMotion['packetRelease']>().parameter(0).toEqualTypeOf<boolean>()
  })

  it('starts an interrupted cover from its current painted transform', async () => {
    const { root, cover, document, clock, motion } = fixture()
    const first = motion.cover('open', false)
    document.paint(cover, {
      transform: 'matrix3d(0.82, 0, 0.57, 0, 0, 1, 0, 0, -0.57, 0, 0.82, 0, -18, 0, 0, 1)',
      boxShadow: 'none',
      filter: 'none',
    })

    const replacement = motion.cover('closed', false)

    await first
    expect(root.style.getPropertyValue('--motion-cover-from-transform')).toBe(
      'matrix3d(0.82, 0, 0.57, 0, 0, 1, 0, 0, -0.57, 0, 0.82, 0, -18, 0, 0, 1)',
    )
    expect(root.dataset.motionCoverKind).toBe('close')
    clock.tick()
    await replacement
    expect(root.style.getPropertyValue('--motion-cover-from-transform')).toBe('')
  })

  it('starts an interrupted record from its complete current painted pose', async () => {
    const { root, record, document, clock, motion } = fixture()
    const first = motion.recordInspection(puzzleId('ossuary-seal'), true, false)
    document.paint(record, {
      transform: 'matrix(0.91, 0, 0, 0.84, 17, -9)',
      boxShadow: 'rgba(12, 7, 9, 0.48) 13px 20px 28px 0px',
      filter: 'brightness(0.98) contrast(1.01)',
    })

    const replacement = motion.recordInspection(puzzleId('ossuary-seal'), false, false)

    await first
    expect(root.style.getPropertyValue('--motion-record-from-transform')).toBe(
      'matrix(0.91, 0, 0, 0.84, 17, -9)',
    )
    expect(root.style.getPropertyValue('--motion-record-from-shadow')).toBe(
      'rgba(12, 7, 9, 0.48) 13px 20px 28px 0px',
    )
    expect(root.style.getPropertyValue('--motion-record-from-filter')).toBe(
      'brightness(0.98) contrast(1.01)',
    )
    expect(root.dataset.motionRecordKind).toBe('return')
    clock.tick()
    await replacement
    expect(root.style.getPropertyValue('--motion-record-from-transform')).toBe('')
    expect(root.style.getPropertyValue('--motion-record-from-shadow')).toBe('')
    expect(root.style.getPropertyValue('--motion-record-from-filter')).toBe('')
  })

  it('lets only the latest replacement clean up its channel', async () => {
    const { root, clock, motion } = fixture()
    const first = motion.dossier(cultureId('seyric'), false)
    const replacement = motion.dossier(cultureId('myratic'), false)

    expect(clock.waits).toHaveLength(1)
    expect(root.dataset.motionDossierTarget).toBe('myratic')
    await first
    expect(root.classList.contains('is-motion-dossier')).toBe(true)
    expect(root.dataset.motionDossierTarget).toBe('myratic')

    clock.tick()
    await replacement
    expect(root.classList.contains('is-motion-dossier')).toBe(false)
    expect(root.dataset.motionDossierTarget).toBeUndefined()
  })

  it('settles every active channel and removes every descriptor synchronously', async () => {
    const { root, clock, motion } = fixture()
    const active = [
      motion.cover('open', false),
      motion.dossier(cultureId('seyric'), false),
      motion.recordInspection(puzzleId('ossuary-seal'), true, false),
      motion.restrictedRefusal(puzzleId('chamber-seal'), false),
      motion.packetRelease(false),
    ]

    motion.settleAll()

    expect(clock.waits).toHaveLength(0)
    expect(Object.keys(root.dataset).filter((name) => name.startsWith('motion'))).toEqual([])
    for (const channel of ['cover', 'dossier', 'record', 'restriction', 'packet']) {
      expect(root.classList.contains(`is-motion-${channel}`)).toBe(false)
      expect(root.style.getPropertyValue(`--motion-${channel}-duration`)).toBe('')
    }
    expect(root.style.getPropertyValue('--motion-cover-from-transform')).toBe('')
    expect(root.style.getPropertyValue('--motion-record-from-transform')).toBe('')
    expect(root.style.getPropertyValue('--motion-record-from-shadow')).toBe('')
    expect(root.style.getPropertyValue('--motion-record-from-filter')).toBe('')
    await Promise.all(active)
  })
})

describe('production folio authored motion timelines', () => {
  it('is the exact approved five-channel and reduced-depth stylesheet', () => {
    const css = readFileSync('src/game/interface/folio-motion.css')
    expect(createHash('sha256').update(css).digest('hex')).toBe(
      '0ff88de58a80d25fb07ea9ea22b334fe906facb4f5fb73d79aaa10f8ccd6bec8',
    )
  })
})
