import {
  decodeTutorialContent,
  type TutorialContentDefinition,
  type TutorialContentRevision,
} from '../src/game/tutorial/content'

export type TutorialEditorActions = {
  readonly currentRevision: () => TutorialContentRevision
  readonly isForeground: () => boolean
  readonly save: (candidateRevision: TutorialContentRevision) => Promise<void>
}

export type TutorialEditorController = {
  edit(definition: TutorialContentDefinition): void
  hide(): void
  readonly isOpen: boolean
  dispose(): void
}

function required<ElementType extends Element>(root: HTMLElement, selector: string): ElementType {
  const element = root.querySelector<ElementType>(selector)
  if (element === null) throw new Error(`missing tutorial editor element '${selector}'`)
  return element
}

function detail(error: unknown): string {
  return error instanceof Error ? error.message : String(error)
}

function isEditableTextControl(element: Element | null): boolean {
  if (element === null) return false
  if (element.tagName === 'INPUT' || element.tagName === 'TEXTAREA') {
    const control = element as HTMLInputElement | HTMLTextAreaElement
    return !control.disabled && !control.readOnly
  }
  return (element as HTMLElement).isContentEditable
}

function candidateRevision(
  current: TutorialContentRevision,
  milestoneId: string,
  text: string,
): TutorialContentRevision {
  if (!current.definitions.some((definition) => definition.milestoneId === milestoneId)) {
    throw new Error(`tutorial milestone '${milestoneId}' no longer exists`)
  }
  return decodeTutorialContent(current.definitions.map((definition) => ({
    milestoneId: definition.milestoneId,
    text: definition.milestoneId === milestoneId ? text : definition.text,
  })))
}

export function mountTutorialEditor(
  root: HTMLElement,
  actions: TutorialEditorActions,
): TutorialEditorController {
  const form = required<HTMLFormElement>(root, '[data-tutorial-editor-form]')
  const id = required<HTMLInputElement>(root, '[data-tutorial-editor-id]')
  const text = required<HTMLTextAreaElement>(root, '[data-tutorial-editor-text]')
  const error = required<HTMLElement>(root, '[data-tutorial-editor-error]')
  const cancel = required<HTMLButtonElement>(root, '[data-tutorial-editor-cancel]')
  const save = required<HTMLButtonElement>(root, '[data-tutorial-editor-save]')
  const controls = [id, text, cancel, save] as const
  const disposers: Array<() => void> = []
  let milestoneId: string | null = null
  let operationPending = false
  let disposed = false
  let generation = 0

  const listen = (target: EventTarget, event: string, listener: EventListener): void => {
    target.addEventListener(event, listener)
    disposers.push(() => target.removeEventListener(event, listener))
  }
  const setOperationPending = (value: boolean): void => {
    operationPending = value
    for (const control of controls) control.disabled = value
  }
  const hide = (): void => {
    generation += 1
    root.hidden = true
    milestoneId = null
    error.textContent = ''
  }
  const hideIfIdle = (): void => {
    if (!operationPending) hide()
  }
  const submit = async (): Promise<void> => {
    if (disposed || operationPending || milestoneId === null) return
    error.textContent = ''
    let candidate: TutorialContentRevision
    try {
      candidate = candidateRevision(actions.currentRevision(), milestoneId, text.value)
    } catch (thrown) {
      error.textContent = `Cannot save tutorial text: ${detail(thrown)}`
      return
    }
    const operationGeneration = generation
    setOperationPending(true)
    try {
      await actions.save(candidate)
      setOperationPending(false)
      if (operationGeneration !== generation) return
      hide()
    } catch (thrown) {
      setOperationPending(false)
      if (operationGeneration !== generation) return
      error.textContent = `Cannot save tutorial text: ${detail(thrown)}`
    }
  }

  listen(form, 'submit', ((event: SubmitEvent): void => {
    event.preventDefault()
    void submit()
  }) as EventListener)
  listen(cancel, 'click', hideIfIdle)
  listen(root.ownerDocument, 'keydown', ((event: KeyboardEvent): void => {
    if (root.hidden || event.code !== 'Backspace' || !actions.isForeground()) return
    const eventTarget = (event.composedPath()[0] ?? event.target) as Element | null
    const editorOwnsFocus = eventTarget === root.ownerDocument.body
      || (eventTarget !== null && root.contains(eventTarget))
    if (!editorOwnsFocus || isEditableTextControl(eventTarget)) return
    event.preventDefault()
    event.stopPropagation()
    hideIfIdle()
  }) as EventListener)
  listen(root, 'keydown', ((event: KeyboardEvent): void => {
    if (root.hidden || event.code !== 'Tab' || operationPending) return
    const activeIndex = controls.findIndex((control) => control === root.ownerDocument.activeElement)
    const nextIndex = event.shiftKey
      ? (activeIndex <= 0 ? controls.length : activeIndex) - 1
      : (activeIndex + 1) % controls.length
    event.preventDefault()
    event.stopPropagation()
    controls[nextIndex]!.focus()
  }) as EventListener)

  return {
    edit(definition) {
      if (disposed || operationPending) return
      generation += 1
      milestoneId = definition.milestoneId
      id.value = definition.milestoneId
      id.readOnly = true
      text.value = definition.text
      error.textContent = ''
      root.hidden = false
      text.focus()
    },
    hide,
    get isOpen() {
      return !root.hidden
    },
    dispose() {
      if (disposed) return
      disposed = true
      generation += 1
      while (disposers.length > 0) disposers.pop()!()
      milestoneId = null
      root.hidden = true
      error.textContent = ''
    },
  }
}
