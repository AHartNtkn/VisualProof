import { describe, expect, it } from 'vitest'
import { attachWorldInput } from '../../game/input'
import { mountToolEditor } from '../../game/tool-editor'
import {
  decodeToolContent,
  LiveToolContent,
  openingToolContent,
  type ToolContentRevision,
} from '../../src/game/tools/content'

class TestElement extends EventTarget {
  hidden = false
  value = ''
  textContent = ''
  readOnly = false
  isContentEditable = false
  parent: EventTarget | null = null
  readonly dataset: Record<string, string> = {}
  readonly children: TestElement[] = []

  constructor(readonly ownerDocument: TestDocument, readonly tagName: string) { super() }

  private disabledValue = false
  get disabled(): boolean { return this.disabledValue }
  set disabled(value: boolean) {
    this.disabledValue = value
    if (value && this.ownerDocument.activeElement === this) this.ownerDocument.activeElement = this.ownerDocument.body
  }

  append(...children: TestElement[]): void {
    for (const child of children) child.parent = this
    this.children.push(...children)
  }

  contains(target: EventTarget | null): boolean {
    return target === this || this.children.some((child) => child.contains(target))
  }

  focus(): void { this.ownerDocument.activeElement = this }

  querySelector<ElementType extends Element>(selector: string): ElementType | null {
    const key = selector.match(/^\[data-([a-z0-9-]+)\]$/)?.[1]
    if (key === undefined) throw new Error(`unsupported selector '${selector}'`)
    const datasetKey = key.replace(/-([a-z])/g, (_whole, letter: string) => letter.toUpperCase())
    if (Object.hasOwn(this.dataset, datasetKey)) return this as unknown as ElementType
    for (const child of this.children) {
      const found = child.querySelector<ElementType>(selector)
      if (found !== null) return found
    }
    return null
  }

  override dispatchEvent(event: Event): boolean {
    if (!Object.hasOwn(event, 'composedPath')) Object.defineProperty(event, 'composedPath', { value: () => [this] })
    const dispatched = super.dispatchEvent(event)
    if (event.bubbles && !event.cancelBubble) this.parent?.dispatchEvent(event)
    return dispatched && !event.defaultPrevented
  }
}

class TestDocument extends EventTarget {
  activeElement: TestElement | null = null
  readonly body = new TestElement(this, 'BODY')
  parent: EventTarget | null = null

  constructor() { super(); this.body.parent = this }
  createElement(tagName: string): TestElement { return new TestElement(this, tagName.toUpperCase()) }
  override dispatchEvent(event: Event): boolean {
    const dispatched = super.dispatchEvent(event)
    if (event.bubbles && !event.cancelBubble) this.parent?.dispatchEvent(event)
    return dispatched && !event.defaultPrevented
  }
}

function element(documentTarget: TestDocument, dataName: string, tagName = 'div'): TestElement {
  const target = documentTarget.createElement(tagName)
  target.dataset[dataName] = ''
  return target
}

function revision(name = 'Iteration', description = 'Duplicate a cutting.'): ToolContentRevision {
  return decodeToolContent(openingToolContent.current.definitions.map((definition) => ({
    ...definition,
    name: definition.id === 'iteration' ? name : definition.name,
    description: definition.id === 'iteration' ? description : definition.description,
  })))
}

type Deferred = { promise: Promise<void>; resolve(): void; reject(error: Error): void }
function deferred(): Deferred {
  let resolve!: () => void
  let reject!: (error: Error) => void
  const promise = new Promise<void>((yes, no) => { resolve = yes; reject = no })
  return { promise, resolve, reject }
}

function harness(initial = revision()) {
  const windowTarget = new EventTarget()
  const documentTarget = new TestDocument()
  documentTarget.parent = windowTarget
  const root = element(documentTarget, 'toolEditor', 'section')
  root.hidden = true
  const form = element(documentTarget, 'toolEditorForm', 'form')
  const id = element(documentTarget, 'toolEditorId', 'input')
  const name = element(documentTarget, 'toolEditorName', 'input')
  const description = element(documentTarget, 'toolEditorDescription', 'textarea')
  const error = element(documentTarget, 'toolEditorError', 'p')
  const cancel = element(documentTarget, 'toolEditorCancel', 'button')
  const save = element(documentTarget, 'toolEditorSave', 'button')
  form.append(id, name, description, error, cancel, save)
  root.append(form)
  documentTarget.body.append(root)
  const live = new LiveToolContent(initial)
  const saved: ToolContentRevision[] = []
  let saveResult = Promise.resolve()
  let foreground = true
  const controller = mountToolEditor(root as unknown as HTMLElement, {
    currentRevision: () => live.current,
    isForeground: () => foreground,
    save: async (candidate) => { saved.push(candidate); await saveResult; live.publish(candidate) },
  })
  return {
    windowTarget, documentTarget, root, form, id, name, description, error, cancel, save,
    live, saved, controller,
    setSaveResult: (result: Promise<void>) => { saveResult = result },
    setForeground: (value: boolean) => { foreground = value },
  }
}

function submit(form: TestElement): void { form.dispatchEvent(new Event('submit', { bubbles: true, cancelable: true })) }
function key(code: string): Event {
  return Object.defineProperty(new Event('keydown', { bubbles: true, cancelable: true }), 'code', { value: code })
}
async function settle(): Promise<void> { await Promise.resolve(); await Promise.resolve() }

describe('tool editor controller', () => {
  it('shows immutable tool identity and publishes one complete edited revision', async () => {
    // Catches editable identity or a detached partial update replacing the whole content authority.
    const h = harness()
    h.controller.edit(h.live.current.definition('iteration'))
    expect(h.id.value).toBe('iteration')
    expect(h.id.readOnly).toBe(true)
    expect(h.name.value).toBe('Iteration')
    expect(h.description.value).toBe('Duplicate a cutting.')

    h.name.value = 'Iteration Loop'
    h.description.value = 'Copies a selected cutting.'
    submit(h.form)
    await settle()

    expect(h.saved).toHaveLength(1)
    expect(h.saved[0]?.definitions).toHaveLength(openingToolContent.current.definitions.length)
    expect(h.saved[0]?.definition('iteration')).toEqual({
      id: 'iteration', name: 'Iteration Loop', description: 'Copies a selected cutting.',
    })
    expect(h.controller.isOpen).toBe(false)
  })

  it('rejects blank name and description while preserving each draft', async () => {
    // Catches invalid authored copy reaching persistence or closing the recovery surface.
    for (const field of ['name', 'description'] as const) {
      const h = harness()
      h.controller.edit(h.live.current.definition('iteration'))
      h[field].value = '   '
      submit(h.form)
      await settle()
      expect(h.saved).toEqual([])
      expect(h.controller.isOpen).toBe(true)
      expect(h[field].value).toBe('   ')
      expect(h.error.textContent).toMatch(/non-blank/i)
    }
  })

  it('keeps the draft and prior live revision after permanent save rejects', async () => {
    // Catches publication-before-persistence or failed writes discarding recoverable edits.
    const initial = revision()
    const gate = deferred()
    const h = harness(initial)
    h.setSaveResult(gate.promise)
    h.controller.edit(initial.definition('iteration'))
    h.name.value = 'Unsaved name'
    h.description.value = 'Unsaved description'
    submit(h.form)
    gate.reject(new Error('repository is read-only'))
    await settle()

    expect(h.controller.isOpen).toBe(true)
    expect(h.name.value).toBe('Unsaved name')
    expect(h.description.value).toBe('Unsaved description')
    expect(h.error.textContent).toContain('repository is read-only')
    expect(h.save.disabled).toBe(false)
    expect(h.live.current).toBe(initial)
  })

  it('gives Backspace to editable text and closes only from noneditable foreground context', () => {
    // Catches text deletion closing the editor or a background draft intercepting Pause input.
    const h = harness()
    h.controller.edit(h.live.current.definition('iteration'))
    h.description.value = 'draft'
    const textBackspace = key('Backspace')
    h.description.dispatchEvent(textBackspace)
    expect(h.controller.isOpen).toBe(true)
    expect(textBackspace.defaultPrevented).toBe(false)

    h.save.focus()
    const close = key('Backspace')
    h.save.dispatchEvent(close)
    expect(h.controller.isOpen).toBe(false)
    expect(close.defaultPrevented).toBe(true)

    h.controller.edit(h.live.current.definition('iteration'))
    h.name.value = 'draft behind Pause'
    h.setForeground(false)
    const background = key('Backspace')
    h.save.dispatchEvent(background)
    expect(h.controller.isOpen).toBe(true)
    expect(h.name.value).toBe('draft behind Pause')
    expect(background.defaultPrevented).toBe(false)
  })

  it('leaves Escape to Pause and preserves the draft through Resume', () => {
    // Catches the editor consuming Escape or resetting the mounted form behind Pause.
    const h = harness()
    let paused = false
    const input = attachWorldInput(h.root as unknown as HTMLElement, {
      pointerDown: () => {}, pointerUp: () => {}, pointerCancel: () => {}, category: () => {},
      toggleLedger: () => {}, stepBack: () => {}, toggleDeveloperMode: () => {},
      pause: () => { paused = true }, engagementChanged: () => {},
    }, { window: h.windowTarget as Window, document: h.documentTarget as unknown as Document })
    input.suspend()
    h.controller.edit(h.live.current.definition('iteration'))
    h.name.value = 'draft behind Pause'
    const escape = key('Escape')
    h.name.dispatchEvent(escape)
    expect(paused).toBe(true)
    expect(h.controller.isOpen).toBe(true)
    input.resume()
    expect(h.name.value).toBe('draft behind Pause')
  })
})
