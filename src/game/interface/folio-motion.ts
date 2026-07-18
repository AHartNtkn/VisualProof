import type { CultureId } from '../types'

export type FolioMotionClock = {
  wait(milliseconds: number, signal: AbortSignal): Promise<void>
}

const browserClock: FolioMotionClock = {
  wait(milliseconds, signal) {
    return new Promise((resolve) => {
      const timer = window.setTimeout(resolve, milliseconds)
      signal.addEventListener('abort', () => {
        window.clearTimeout(timer)
        resolve()
      }, { once: true })
    })
  },
}

type ActiveDossierMotion = {
  readonly controller: AbortController
  readonly generation: number
}

export class FolioDossierMotion {
  private active: ActiveDossierMotion | null = null
  private activeRestriction: ActiveDossierMotion | null = null
  private generation = 0
  private restrictionGeneration = 0

  constructor(
    private readonly root: HTMLElement,
    private readonly clock: FolioMotionClock = browserClock,
  ) {}

  async replace(culture: CultureId, reducedMotion: boolean): Promise<void> {
    this.generation += 1
    this.active?.controller.abort()
    this.active = null
    this.settlePresentation()
    if (reducedMotion) return

    const active: ActiveDossierMotion = {
      controller: new AbortController(),
      generation: this.generation,
    }
    this.active = active
    this.root.classList.add('is-motion-dossier')
    this.root.dataset.motionDossierTarget = culture
    this.root.style.setProperty('--folio-dossier-duration', '260ms')
    try {
      await this.clock.wait(260, active.controller.signal)
    } finally {
      if (this.active === active && active.generation === this.generation) {
        this.active = null
        this.settlePresentation()
      }
    }
  }

  async restrictedRefusal(target: string, reducedMotion: boolean): Promise<void> {
    this.restrictionGeneration += 1
    this.activeRestriction?.controller.abort()
    this.activeRestriction = null
    this.settleRestrictionPresentation()
    const active: ActiveDossierMotion = {
      controller: new AbortController(),
      generation: this.restrictionGeneration,
    }
    this.activeRestriction = active
    this.root.classList.add('is-motion-restriction')
    this.root.dataset.motionRestrictionTarget = target
    this.root.dataset.motionRestrictionKind = reducedMotion ? 'reduced' : 'refuse'
    const duration = reducedMotion ? 90 : 320
    this.root.style.setProperty('--motion-restriction-duration', `${duration}ms`)
    try {
      await this.clock.wait(duration, active.controller.signal)
    } finally {
      if (
        this.activeRestriction === active
        && active.generation === this.restrictionGeneration
      ) {
        this.activeRestriction = null
        this.settleRestrictionPresentation()
      }
    }
  }

  settleRestriction(): void {
    this.restrictionGeneration += 1
    this.activeRestriction?.controller.abort()
    this.activeRestriction = null
    this.settleRestrictionPresentation()
  }

  settle(): void {
    this.generation += 1
    this.active?.controller.abort()
    this.active = null
    this.settlePresentation()
    this.settleRestriction()
  }

  private settlePresentation(): void {
    this.root.classList.remove('is-motion-dossier')
    delete this.root.dataset.motionDossierTarget
    this.root.style.removeProperty('--folio-dossier-duration')
  }

  private settleRestrictionPresentation(): void {
    this.root.classList.remove('is-motion-restriction')
    delete this.root.dataset.motionRestrictionTarget
    delete this.root.dataset.motionRestrictionKind
    this.root.style.removeProperty('--motion-restriction-duration')
  }
}
