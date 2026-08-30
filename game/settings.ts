export type SettingsState = {
  readonly tutorialsEnabled: boolean
  readonly developerToolsEnabled: boolean
}

export type SettingsActions = {
  readonly setTutorialsEnabled: (enabled: boolean) => void
  readonly setDeveloperToolsEnabled: (enabled: boolean) => void
  readonly back: () => void
}

export type SettingsController = {
  show(state: SettingsState): void
  hide(): void
  dispose(): void
}

export type DeveloperToolsSettingPorts = {
  readonly persist: (enabled: boolean) => void
  readonly setDeveloperMode: (enabled: boolean) => void
  readonly hideForegroundEditors: () => void
  readonly clearForegroundEditor: () => void
  readonly renderTutorial: () => void
  readonly refreshVisibleLedger: () => void
  readonly mirrorRuntimeState: () => void
}

type HideableEditor = { hide(): void }

export type DeveloperToolsRuntimePorts = Omit<
  DeveloperToolsSettingPorts,
  'hideForegroundEditors'
> & {
  readonly orderEditor: () => HideableEditor | null
  readonly tutorialEditor: () => HideableEditor | null
  readonly toolEditor: () => HideableEditor | null
}

export function developerToolsSettingPorts(
  ports: DeveloperToolsRuntimePorts,
): DeveloperToolsSettingPorts {
  const { orderEditor, tutorialEditor, toolEditor, ...settingPorts } = ports
  return {
    ...settingPorts,
    hideForegroundEditors: () => {
      orderEditor()?.hide()
      tutorialEditor()?.hide()
      toolEditor()?.hide()
    },
  }
}

export function applyDeveloperToolsSetting(
  enabled: boolean,
  ports: DeveloperToolsSettingPorts,
): void {
  ports.persist(enabled)
  if (!enabled) {
    ports.setDeveloperMode(false)
    ports.hideForegroundEditors()
    ports.clearForegroundEditor()
  }
  ports.renderTutorial()
  ports.refreshVisibleLedger()
  ports.mirrorRuntimeState()
}

function required<ElementType extends Element>(root: HTMLElement, selector: string): ElementType {
  const element = root.querySelector<ElementType>(selector)
  if (element === null) throw new Error(`missing settings element '${selector}'`)
  return element
}

export function mountSettings(root: HTMLElement, actions: SettingsActions): SettingsController {
  const tutorials = required<HTMLInputElement>(root, '[data-settings-tutorials]')
  const developerTools = required<HTMLInputElement>(root, '[data-settings-developer-tools]')
  const back = required<HTMLButtonElement>(root, '[data-settings-back]')
  const controls = [tutorials, developerTools, back] as const
  const disposers: Array<() => void> = []

  const listen = (target: EventTarget, type: string, listener: EventListener): void => {
    target.addEventListener(type, listener)
    disposers.push(() => target.removeEventListener(type, listener))
  }
  const returnToPause = (): void => {
    if (root.hidden) return
    root.hidden = true
    actions.back()
  }

  listen(tutorials, 'change', () => {
    if (!root.hidden) actions.setTutorialsEnabled(tutorials.checked)
  })
  listen(developerTools, 'change', () => {
    if (!root.hidden) actions.setDeveloperToolsEnabled(developerTools.checked)
  })
  listen(back, 'click', returnToPause)
  listen(root, 'keydown', ((event: KeyboardEvent): void => {
    if (root.hidden) return
    if (event.code === 'Escape') {
      event.preventDefault()
      event.stopPropagation()
      returnToPause()
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
    show(state) {
      tutorials.checked = state.tutorialsEnabled
      developerTools.checked = state.developerToolsEnabled
      root.hidden = false
      tutorials.focus()
    },
    hide() {
      root.hidden = true
    },
    dispose() {
      while (disposers.length > 0) disposers.pop()!()
      root.hidden = true
    },
  }
}
