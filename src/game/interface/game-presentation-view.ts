import type {
  ActiveGuidance,
  CompletionReceipt,
  GamePrimaryMode,
  GameSettings,
  GameTransient,
} from '../controller-state'
import type { GameAction } from '../controller'
import './game-presentation-view.css'

export type GamePresentationProjection = {
  readonly mode: GamePrimaryMode
  readonly transient: GameTransient | null
  readonly guidance: ActiveGuidance | null
  readonly settings: GameSettings
  readonly completion: {
    readonly receipt: CompletionReceipt
    readonly artifactName: string
    readonly response: string
  } | null
}

export type MountedGamePresentationView = {
  readonly element: HTMLElement
  update(projection: GamePresentationProjection): void
  dispose(): void
}

const element = <K extends keyof HTMLElementTagNameMap>(
  document: Document,
  tag: K,
  className?: string,
): HTMLElementTagNameMap[K] => {
  const created = document.createElement(tag)
  if (className !== undefined) created.className = className
  return created
}

const actionButton = (
  document: Document,
  text: string,
  action: GameAction,
  dispatch: (action: GameAction) => void,
): HTMLButtonElement => {
  const button = element(document, 'button', 'curse-presentation-action')
  button.type = 'button'
  button.textContent = text
  button.addEventListener('click', () => dispatch(action))
  return button
}

export function mountGamePresentationView(options: {
  readonly host: HTMLElement
  readonly projection: GamePresentationProjection
  readonly dispatch: (action: GameAction) => void
}): MountedGamePresentationView {
  const document = options.host.ownerDocument
  const root = element(document, 'div', 'curse-game-presentation')
  options.host.append(root)

  const renderGuidance = (projection: GamePresentationProjection): HTMLElement | null => {
    const guidance = projection.guidance
    if (projection.mode !== 'puzzle' || guidance === null || projection.transient !== null) {
      return null
    }
    const note = element(document, 'aside', 'curse-guidance-note')
    const paragraph = element(document, 'p')
    paragraph.dataset.guidanceText = ''
    paragraph.textContent = guidance.intervention.pages[guidance.page] ?? ''
    note.append(paragraph)
    const lastPage = guidance.intervention.pages.length - 1
    if (lastPage > 0) {
      const footer = element(document, 'div', 'curse-guidance-footer')
      const position = element(document, 'span', 'curse-guidance-position')
      position.textContent = `${guidance.page + 1} / ${guidance.intervention.pages.length}`
      footer.append(position)
      if (guidance.page < lastPage) {
        footer.append(actionButton(
          document,
          'Next',
          { kind: 'advanceGuidancePage' },
          options.dispatch,
        ))
      }
      note.append(footer)
    }
    return note
  }

  const renderPauseMenu = (): HTMLElement => {
    const panel = element(document, 'section', 'curse-pause-panel curse-pause-menu')
    panel.setAttribute('role', 'dialog')
    panel.setAttribute('aria-modal', 'true')
    panel.setAttribute('aria-labelledby', 'curse-pause-heading')
    const heading = element(document, 'h1')
    heading.id = 'curse-pause-heading'
    heading.textContent = 'Work suspended'
    const actions = element(document, 'div', 'curse-pause-actions')
    actions.append(
      actionButton(document, 'Resume', { kind: 'resume' }, options.dispatch),
      actionButton(document, 'Level selection', { kind: 'levelSelection' }, options.dispatch),
      actionButton(document, 'Settings', { kind: 'openPauseSettings' }, options.dispatch),
      actionButton(document, 'Exit game', { kind: 'exitGame' }, options.dispatch),
    )
    panel.append(heading, actions)
    return panel
  }

  const renderSettings = (settings: GameSettings): HTMLElement => {
    const panel = element(document, 'section', 'curse-pause-panel curse-pause-settings')
    panel.setAttribute('role', 'dialog')
    panel.setAttribute('aria-modal', 'true')
    panel.setAttribute('aria-labelledby', 'curse-settings-heading')
    const heading = element(document, 'h1')
    heading.id = 'curse-settings-heading'
    heading.textContent = 'Instrument settings'

    const reduced = element(document, 'label', 'curse-setting')
    reduced.dataset.setting = 'reduced-motion'
    const reducedInput = element(document, 'input')
    reducedInput.type = 'checkbox'
    reducedInput.checked = settings.reducedMotion
    reducedInput.addEventListener('change', () => options.dispatch({
      kind: 'setReducedMotion', value: reducedInput.checked,
    }))
    reduced.append(reducedInput, document.createTextNode(' Reduced motion'))

    const fullscreen = element(document, 'label', 'curse-setting')
    fullscreen.dataset.setting = 'fullscreen'
    const fullscreenInput = element(document, 'input')
    fullscreenInput.type = 'checkbox'
    fullscreenInput.checked = settings.fullscreen
    fullscreenInput.addEventListener('change', () => options.dispatch({
      kind: 'setFullscreen', value: fullscreenInput.checked,
    }))
    fullscreen.append(fullscreenInput, document.createTextNode(' Fullscreen'))

    const textSize = element(document, 'label', 'curse-setting')
    textSize.dataset.setting = 'text-size'
    textSize.append(document.createTextNode('Interface text size '))
    const select = element(document, 'select')
    for (const value of ['small', 'medium', 'large'] as const) {
      const option = element(document, 'option')
      option.value = value
      option.textContent = value[0]!.toUpperCase() + value.slice(1)
      select.append(option)
    }
    select.value = settings.textSize
    select.addEventListener('change', () => options.dispatch({
      kind: 'setTextSize', value: select.value as GameSettings['textSize'],
    }))
    textSize.append(select)

    panel.append(
      heading,
      reduced,
      fullscreen,
      textSize,
      actionButton(document, 'Back', { kind: 'escape' }, options.dispatch),
    )
    return panel
  }

  const renderCompletion = (
    completion: NonNullable<GamePresentationProjection['completion']>,
  ): HTMLElement => {
    const panel = element(document, 'section', 'curse-completion')
    panel.setAttribute('aria-labelledby', 'curse-completion-heading')
    const line = element(document, 'p', 'curse-completion-line')
    line.dataset.completionLine = ''
    line.textContent = 'Restoration complete'
    const heading = element(document, 'h1')
    heading.id = 'curse-completion-heading'
    heading.textContent = completion.artifactName
    const moves = element(document, 'p', 'curse-completion-moves')
    moves.dataset.completionMoves = ''
    moves.textContent = `${completion.receipt.moves} ${completion.receipt.moves === 1 ? 'move' : 'moves'}`
    const response = element(document, 'blockquote', 'curse-completion-response')
    response.dataset.completionResponse = ''
    response.textContent = completion.response
    panel.append(
      line,
      heading,
      moves,
      response,
      actionButton(
        document,
        'Return to level selection',
        { kind: 'levelSelection' },
        options.dispatch,
      ),
    )
    return panel
  }

  const render = (projection: GamePresentationProjection): void => {
    root.replaceChildren()
    const transient = projection.transient
    if (transient?.kind === 'pause') {
      const scrim = element(document, 'div', 'curse-pause-scrim')
      scrim.append(transient.presentation === 'settings'
        ? renderSettings(projection.settings)
        : renderPauseMenu())
      root.append(scrim)
      return
    }
    if (projection.mode === 'completion' && projection.completion !== null) {
      root.append(renderCompletion(projection.completion))
      return
    }
    const guidance = renderGuidance(projection)
    if (guidance !== null) root.append(guidance)
  }

  render(options.projection)
  let disposed = false
  return {
    element: root,
    update: render,
    dispose() {
      if (disposed) return
      disposed = true
      root.remove()
    },
  }
}
