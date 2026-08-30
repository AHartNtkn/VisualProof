import { snapshotFromDiagram, type DiagramSnapshot } from '../src/game/diagram-snapshot'
import {
  decodeOrderCatalog,
  type OrderCatalogRevision,
  type OrderDefinition,
} from '../src/game/orders/catalog'
import { formulaToDiagram } from '../src/formula'
import { diagramToJson } from '../src/kernel/diagram'
import { DiagramBuilder } from '../src/kernel/diagram/builder'
import { renderDiagramPreview } from './diagram-preview'

export type OrderEditorActions = {
  readonly currentRevision: () => OrderCatalogRevision
  readonly save: (candidateRevision: OrderCatalogRevision) => Promise<void>
  readonly delete: (orderId: string) => Promise<void>
}

export type OrderEditorController = {
  edit(definition: OrderDefinition): void
  create(): void
  hide(): void
  readonly isOpen: boolean
  dispose(): void
}

type EditorMode =
  | { readonly kind: 'edit'; readonly orderId: string; readonly goal: DiagramSnapshot }
  | { readonly kind: 'create'; readonly goal: DiagramSnapshot }

type SerializedDefinition = {
  readonly id: string
  readonly prerequisites: readonly string[]
  readonly reward: number
  readonly goal: unknown
  readonly formula?: string
}

function required<ElementType extends Element>(root: HTMLElement, selector: string): ElementType {
  const element = root.querySelector<ElementType>(selector)
  if (element === null) throw new Error(`missing order editor element '${selector}'`)
  return element
}

function candidateGoal(
  current: DiagramSnapshot,
  formulaInput: string,
): { readonly goal: DiagramSnapshot; readonly formula?: string } {
  if (formulaInput.trim().length === 0) return { goal: current }
  return { goal: snapshotFromDiagram(formulaToDiagram(formulaInput)), formula: formulaInput }
}

function parsePrerequisites(input: string): readonly string[] {
  if (input.trim().length === 0) return []
  const parsed = input.split(/[\n,]/).map((entry) => entry.trim())
  if (parsed.some((entry) => entry.length === 0)) {
    throw new Error('prerequisites contain a blank prerequisite')
  }
  const seen = new Set<string>()
  for (const prerequisite of parsed) {
    if (seen.has(prerequisite)) throw new Error(`duplicate prerequisite '${prerequisite}'`)
    seen.add(prerequisite)
  }
  return parsed
}

function parseReward(input: string): number {
  if (!/^(0|[1-9]\d*)$/.test(input.trim())) {
    throw new Error('reward must be a nonnegative safe integer')
  }
  const parsed = Number(input.trim())
  if (!Number.isSafeInteger(parsed)) throw new Error('reward must be a nonnegative safe integer')
  return parsed
}

function serializedDefinition(definition: OrderDefinition): SerializedDefinition {
  const shared = {
    id: definition.id,
    prerequisites: [...definition.prerequisites],
    reward: definition.reward,
    goal: diagramToJson(definition.goal.diagram),
  }
  return definition.formula === undefined ? shared : { ...shared, formula: definition.formula }
}

function candidateRevision(
  current: OrderCatalogRevision,
  mode: EditorMode,
  definition: SerializedDefinition,
): OrderCatalogRevision {
  const serialized = current.definitions.map(serializedDefinition)
  if (mode.kind === 'create') return decodeOrderCatalog([...serialized, definition])
  const index = serialized.findIndex(({ id }) => id === mode.orderId)
  if (index < 0) throw new Error(`order '${mode.orderId}' no longer exists`)
  return decodeOrderCatalog(serialized.map((entry, entryIndex) => (
    entryIndex === index ? definition : entry
  )))
}

function deletionCandidate(current: OrderCatalogRevision, orderId: string): OrderCatalogRevision {
  if (!current.byId.has(orderId)) throw new Error(`order '${orderId}' no longer exists`)
  return decodeOrderCatalog(
    current.definitions
      .filter((definition) => definition.id !== orderId)
      .map(serializedDefinition),
  )
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

export function mountOrderEditor(
  root: HTMLElement,
  actions: OrderEditorActions,
): OrderEditorController {
  const title = required<HTMLElement>(root, '[data-order-editor-title]')
  const form = required<HTMLFormElement>(root, '[data-order-editor-form]')
  const id = required<HTMLInputElement>(root, '[data-order-editor-id]')
  const prerequisites = required<HTMLTextAreaElement>(root, '[data-order-editor-prerequisites]')
  const reward = required<HTMLInputElement>(root, '[data-order-editor-reward]')
  const formula = required<HTMLTextAreaElement>(root, '[data-order-editor-formula]')
  const preview = required<HTMLCanvasElement>(root, '[data-order-editor-preview]')
  const error = required<HTMLElement>(root, '[data-order-editor-error]')
  const remove = required<HTMLButtonElement>(root, '[data-order-editor-delete]')
  const cancel = required<HTMLButtonElement>(root, '[data-order-editor-cancel]')
  const save = required<HTMLButtonElement>(root, '[data-order-editor-save]')
  const controls = [id, prerequisites, reward, formula, remove, cancel, save] as const
  const disposers: Array<() => void> = []
  let mode: EditorMode | null = null
  let operationPending = false
  let disposed = false
  let generation = 0

  const listen = (target: EventTarget, type: string, listener: EventListener): void => {
    target.addEventListener(type, listener)
    disposers.push(() => target.removeEventListener(type, listener))
  }
  const setOperationPending = (value: boolean): void => {
    operationPending = value
    for (const control of controls) control.disabled = value
  }
  const showError = (operation: 'save' | 'delete', thrown: unknown): void => {
    error.textContent = `Cannot ${operation} order: ${detail(thrown)}`
  }
  const showPreview = (snapshot: DiagramSnapshot): void => {
    preview.dataset['diagramSnapshot'] = snapshot.json
    renderDiagramPreview(preview, snapshot)
  }
  const hide = (): void => {
    generation += 1
    root.hidden = true
    mode = null
    error.textContent = ''
  }
  const hideIfIdle = (): void => {
    if (!operationPending) hide()
  }
  const submit = async (): Promise<void> => {
    if (disposed || operationPending || mode === null) return
    error.textContent = ''
    let candidate: OrderCatalogRevision
    let candidatePreview: DiagramSnapshot
    const authoritativePreview = mode.goal
    try {
      const goal = candidateGoal(mode.goal, formula.value)
      candidatePreview = goal.goal
      const shared = {
        id: mode.kind === 'edit' ? mode.orderId : id.value,
        prerequisites: parsePrerequisites(prerequisites.value),
        reward: parseReward(reward.value),
        goal: diagramToJson(goal.goal.diagram),
      }
      candidate = candidateRevision(
        actions.currentRevision(),
        mode,
        goal.formula === undefined ? shared : { ...shared, formula: goal.formula },
      )
    } catch (thrown) {
      showError('save', thrown)
      return
    }
    showPreview(candidatePreview)
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
      showPreview(authoritativePreview)
      showError('save', thrown)
    }
  }
  const deleteOrder = async (): Promise<void> => {
    if (disposed || operationPending || mode?.kind !== 'edit') return
    error.textContent = ''
    try {
      deletionCandidate(actions.currentRevision(), mode.orderId)
    } catch (thrown) {
      showError('delete', thrown)
      return
    }
    const orderId = mode.orderId
    const operationGeneration = generation
    setOperationPending(true)
    try {
      await actions.delete(orderId)
      setOperationPending(false)
      if (operationGeneration !== generation) return
      hide()
    } catch (thrown) {
      setOperationPending(false)
      if (operationGeneration !== generation) return
      showError('delete', thrown)
    }
  }

  listen(form, 'submit', ((event: SubmitEvent): void => {
    event.preventDefault()
    void submit()
  }) as EventListener)
  listen(remove, 'click', () => { void deleteOrder() })
  listen(cancel, 'click', hideIfIdle)
  listen(root, 'keydown', ((event: KeyboardEvent): void => {
    if (root.hidden) return
    if (event.code === 'Backspace') {
      if (isEditableTextControl(root.ownerDocument.activeElement)) return
      event.preventDefault()
      event.stopPropagation()
      hideIfIdle()
      return
    }
    if (event.code !== 'Tab' || operationPending) return
    const visibleControls = controls.filter((control) => !control.hidden)
    const activeIndex = visibleControls.findIndex((control) => control === root.ownerDocument.activeElement)
    const nextIndex = event.shiftKey
      ? (activeIndex <= 0 ? visibleControls.length : activeIndex) - 1
      : (activeIndex + 1) % visibleControls.length
    event.preventDefault()
    event.stopPropagation()
    visibleControls[nextIndex]!.focus()
  }) as EventListener)

  const show = (nextMode: EditorMode, definition?: OrderDefinition): void => {
    if (disposed || operationPending) return
    generation += 1
    mode = nextMode
    error.textContent = ''
    root.hidden = false
    if (nextMode.kind === 'edit') {
      title.textContent = 'Edit order'
      id.value = definition!.id
      id.readOnly = true
      prerequisites.value = definition!.prerequisites.join(', ')
      reward.value = String(definition!.reward)
      formula.value = definition!.formula ?? ''
      remove.hidden = false
      save.textContent = 'Save changes'
      showPreview(definition!.goal)
      prerequisites.focus()
      return
    }
    title.textContent = 'Create order'
    id.value = ''
    id.readOnly = false
    prerequisites.value = ''
    reward.value = '1'
    formula.value = ''
    remove.hidden = true
    save.textContent = 'Create order'
    showPreview(nextMode.goal)
    id.focus()
  }

  return {
    edit(definition) {
      show({ kind: 'edit', orderId: definition.id, goal: definition.goal }, definition)
    },
    create() {
      show({ kind: 'create', goal: snapshotFromDiagram(new DiagramBuilder().build()) })
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
      mode = null
      root.hidden = true
      error.textContent = ''
    },
  }
}
