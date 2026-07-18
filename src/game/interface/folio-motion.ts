import type { CultureId, PuzzleId } from '../types'

export type FolioMotionClock = {
  wait(milliseconds: number, signal: AbortSignal): Promise<void>
}

type CoverState = 'open' | 'closed'
type MotionChannel = 'cover' | 'dossier' | 'record' | 'restriction' | 'packet'

type ActiveMotion = {
  controller: AbortController
  cancel: () => void
}

type InterruptedSnapshot = Record<string, string>

const snapshotSubjects: Partial<
  Record<
    MotionChannel,
    {
      selector: string
      properties: Array<{ style: 'transform' | 'boxShadow' | 'filter'; variable: string }>
    }
  >
> = {
  cover: {
    selector: '.cover-surface',
    properties: [{ style: 'transform', variable: '--motion-cover-from-transform' }],
  },
  record: {
    selector: '.inspection-record',
    properties: [
      { style: 'transform', variable: '--motion-record-from-transform' },
      { style: 'boxShadow', variable: '--motion-record-from-shadow' },
      { style: 'filter', variable: '--motion-record-from-filter' },
    ],
  },
}

const fullDurations: Record<MotionChannel, number> = {
  cover: 380,
  dossier: 260,
  record: 340,
  restriction: 320,
  packet: 480,
}
const reducedDuration = 90

const browserClock: FolioMotionClock = {
  wait(milliseconds, signal) {
    return new Promise((resolve) => {
      const timeout = window.setTimeout(resolve, milliseconds)
      signal.addEventListener(
        'abort',
        () => {
          window.clearTimeout(timeout)
          resolve()
        },
        { once: true },
      )
    })
  },
}

export class FolioMotion {
  private readonly active = new Map<MotionChannel, ActiveMotion>()

  constructor(
    private readonly root: HTMLElement,
    private readonly clock: FolioMotionClock = browserClock,
  ) {}

  cover(target: CoverState, reducedMotion: boolean): Promise<void> {
    return this.run('cover', target, target === 'open' ? 'open' : 'close', reducedMotion)
  }

  dossier(target: CultureId, reducedMotion: boolean): Promise<void> {
    return this.run('dossier', target, 'replace', reducedMotion)
  }

  recordInspection(
    target: PuzzleId,
    inspecting: boolean,
    reducedMotion: boolean,
  ): Promise<void> {
    return this.run('record', target, inspecting ? 'inspect' : 'return', reducedMotion)
  }

  restrictedRefusal(target: PuzzleId | CultureId, reducedMotion: boolean): Promise<void> {
    return this.run('restriction', target, 'refuse', reducedMotion)
  }

  packetRelease(reducedMotion: boolean): Promise<void> {
    return this.run('packet', 'myratic', 'release', reducedMotion)
  }

  settleAll(): void {
    for (const channel of this.channels()) this.cancel(channel)
  }

  private async run(
    channel: MotionChannel,
    target: string,
    kind: string,
    reducedMotion: boolean,
  ): Promise<void> {
    const interruptedSnapshot = this.captureInterruptedSnapshot(channel)
    this.cancel(channel)

    const duration = reducedMotion ? reducedDuration : fullDurations[channel]
    const controller = new AbortController()
    const active: ActiveMotion = {
      controller,
      cancel: () => controller.abort(),
    }
    this.active.set(channel, active)
    this.applyInterruptedSnapshot(interruptedSnapshot)
    this.root.classList.add(this.className(channel))
    this.root.dataset[this.targetKey(channel)] = target
    this.root.dataset[this.kindKey(channel)] = reducedMotion ? 'reduced' : kind
    this.root.style.setProperty(this.durationProperty(channel), `${duration}ms`)

    try {
      await this.clock.wait(duration, controller.signal)
    } finally {
      if (this.active.get(channel) === active) this.cleanup(channel)
    }
  }

  private cancel(channel: MotionChannel): void {
    const active = this.active.get(channel)
    if (active !== undefined) {
      this.active.delete(channel)
      active.cancel()
    }
    this.cleanup(channel)
  }

  private cleanup(channel: MotionChannel): void {
    this.active.delete(channel)
    delete this.root.dataset[this.targetKey(channel)]
    delete this.root.dataset[this.kindKey(channel)]
    this.root.style.removeProperty(this.durationProperty(channel))
    for (const property of snapshotSubjects[channel]?.properties ?? []) {
      this.root.style.removeProperty(property.variable)
    }
    this.root.classList.remove(this.className(channel))
  }

  private captureInterruptedSnapshot(channel: MotionChannel): InterruptedSnapshot {
    if (!this.active.has(channel)) return {}
    const subject = snapshotSubjects[channel]
    const element = subject === undefined
      ? null
      : this.root.querySelector<HTMLElement>(subject.selector)
    const view = this.root.ownerDocument.defaultView
    if (subject === undefined || element === null || view === null) return {}
    const computed = view.getComputedStyle(element)
    return Object.fromEntries(
      subject.properties.map(({ style, variable }) => [variable, computed[style]]),
    )
  }

  private applyInterruptedSnapshot(snapshot: InterruptedSnapshot): void {
    for (const [property, value] of Object.entries(snapshot)) {
      this.root.style.setProperty(property, value)
    }
  }

  private targetKey(channel: MotionChannel): string {
    return `motion${capitalize(channel)}Target`
  }

  private kindKey(channel: MotionChannel): string {
    return `motion${capitalize(channel)}Kind`
  }

  private durationProperty(channel: MotionChannel): string {
    return `--motion-${channel}-duration`
  }

  private className(channel: MotionChannel): string {
    return `is-motion-${channel}`
  }

  private channels(): MotionChannel[] {
    return ['cover', 'dossier', 'record', 'restriction', 'packet']
  }
}

function capitalize(value: string): string {
  return `${value[0]?.toUpperCase() ?? ''}${value.slice(1)}`
}
