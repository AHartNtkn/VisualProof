import {
  decodeToolContent,
  type ToolContentDefinition,
  type ToolContentRevision,
} from '../src/game/tools/content'

export type ToolEditorActions = {
  readonly currentRevision: () => ToolContentRevision
  readonly isForeground: () => boolean
  readonly save: (candidateRevision: ToolContentRevision) => Promise<void>
}

export type ToolEditorController = {
  edit(definition: ToolContentDefinition): void
  hide(): void
  readonly isOpen: boolean
  dispose(): void
}

function required<ElementType extends Element>(root: HTMLElement, selector: string): ElementType {
  const element = root.querySelector<ElementType>(selector)
  if (element === null) throw new Error(`missing tool editor element '${selector}'`)
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
  current: ToolContentRevision,
  toolId: string,
  name: string,
  description: string,
): ToolContentRevision {
  if (!current.definitions.some((definition) => definition.id === toolId)) {
    throw new Error(`tool '${toolId}' no longer exists`)
  }
  return decodeToolContent(current.definitions.map((definition) => ({
    id: definition.id,
    name: definition.id === toolId ? name : definition.name,
    description: definition.id === toolId ? description : definition.description,
  })))
}

export function mountToolEditor(
  root: HTMLElement,
  actions: ToolEditorActions,
): ToolEditorController {
  const form = required<HTMLFormElement>(root, '[data-tool-editor-form]')
  const id = required<HTMLInputElement>(root, '[data-tool-editor-id]')
  const name = required<HTMLInputElement>(root, '[data-tool-editor-name]')
  const description = required<HTMLTextAreaElement>(root, '[data-tool-editor-description]')
  const error = required<HTMLElement>(root, '[data-tool-editor-error]')
  const cancel = required<HTMLButtonElement>(root, '[data-tool-editor-cancel]')
  const save = required<HTMLButtonElement>(root, '[data-tool-editor-save]')
  const controls = [id, name, description, cancel, save] as const
  const disposers: Array<() => void> = []
  let toolId: string | null = null
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
    toolId = null
    error.textContent = ''
  }
  const hideIfIdle = (): void => {
    if (!operationPending) hide()
  }
  const submit = async (): Promise<void> => {
    if (disposed || operationPending || toolId === null) return
    error.textContent = ''
    let candidate: ToolContentRevision
    try {
      candidate = candidateRevision(actions.currentRevision(), toolId, name.value, description.value)
    } catch (thrown) {
      error.textContent = `Cannot save tool content: ${detail(thrown)}`
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
      error.textContent = `Cannot save tool content: ${detail(thrown)}`
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
      toolId = definition.id
      id.value = definition.id
      id.readOnly = true
      name.value = definition.name
      description.value = definition.description
      error.textContent = ''
      root.hidden = false
      name.focus()
    },
    hide,
    get isOpen() { return !root.hidden },
    dispose() {
      if (disposed) return
      disposed = true
      generation += 1
      while (disposers.length > 0) disposers.pop()!()
      toolId = null
      root.hidden = true
      error.textContent = ''
    },
  }
}
