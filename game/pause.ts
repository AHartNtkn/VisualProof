export type PauseMenuActions = {
  readonly resume: () => void
  readonly settings: () => void
  readonly mainMenu: () => Promise<void>
  readonly quit: () => Promise<void>
}

export type PauseMenuController = {
  show(worldName: string): void
  hide(): void
  dispose(): void
}

function required<ElementType extends Element>(root: HTMLElement, selector: string): ElementType {
  const element = root.querySelector<ElementType>(selector)
  if (element === null) throw new Error(`missing pause menu element '${selector}'`)
  return element
}

function detail(error: unknown): string {
  return error instanceof Error ? error.message : String(error)
}

export function mountPauseMenu(
  root: HTMLElement,
  actions: PauseMenuActions,
): PauseMenuController {
  const worldName = required<HTMLElement>(root, '[data-pause-world-name]')
  const error = required<HTMLElement>(root, '[data-pause-error]')
  const resume = required<HTMLButtonElement>(root, '[data-pause-resume]')
  const settings = required<HTMLButtonElement>(root, '[data-pause-settings]')
  const mainMenu = required<HTMLButtonElement>(root, '[data-pause-main-menu]')
  const quit = required<HTMLButtonElement>(root, '[data-pause-quit]')
  const controls = [resume, settings, mainMenu, quit] as const
  const disposers: Array<() => void> = []
  let busy = false

  const listen = (target: EventTarget, type: string, listener: EventListener): void => {
    target.addEventListener(type, listener)
    disposers.push(() => target.removeEventListener(type, listener))
  }
  const setBusy = (next: boolean): void => {
    busy = next
    for (const control of controls) control.disabled = next
  }
  const run = (label: string, action: () => Promise<void>): void => {
    if (busy) return
    error.textContent = ''
    setBusy(true)
    void action().catch((failure: unknown) => {
      error.textContent = `Could not ${label}: ${detail(failure)}`
      setBusy(false)
      resume.focus()
    })
  }
  const resumeGame = (): void => {
    if (!busy && !root.hidden) actions.resume()
  }

  listen(resume, 'click', resumeGame)
  listen(settings, 'click', () => {
    if (!busy && !root.hidden) actions.settings()
  })
  listen(mainMenu, 'click', () => run('return to main menu', actions.mainMenu))
  listen(quit, 'click', () => run('quit game', actions.quit))
  listen(root, 'keydown', ((event: KeyboardEvent): void => {
    if (root.hidden || busy) return
    if (event.code === 'Escape') {
      event.preventDefault()
      event.stopPropagation()
      resumeGame()
      return
    }
    if (event.code !== 'Tab') return
    const active = root.ownerDocument.activeElement
    const index = controls.findIndex((control) => control === active)
    const next = event.shiftKey
      ? controls[(index <= 0 ? controls.length : index) - 1]!
      : controls[(index + 1) % controls.length]!
    event.preventDefault()
    event.stopPropagation()
    next.focus()
  }) as EventListener)

  return {
    show(name) {
      worldName.textContent = name
      error.textContent = ''
      setBusy(false)
      root.hidden = false
      resume.focus()
    },
    hide() {
      root.hidden = true
      error.textContent = ''
      setBusy(false)
    },
    dispose() {
      while (disposers.length > 0) disposers.pop()!()
      root.hidden = true
      setBusy(false)
    },
  }
}
