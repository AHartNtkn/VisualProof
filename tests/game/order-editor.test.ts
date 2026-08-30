import { describe, expect, it } from 'vitest'
import { attachWorldInput } from '../../game/input'
import { mountOrderEditor } from '../../game/order-editor'
import {
  decodeOrderCatalog,
  LiveOrderCatalog,
  type OrderCatalogRevision,
} from '../../src/game/orders/catalog'
import { diagramToJson } from '../../src/kernel/diagram'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { formulaToDiagram } from '../../src/formula'

class TestElement extends EventTarget {
  public hidden = false
  public value = ''
  public textContent = ''
  public type = ''
  public className = ''
  public readOnly = false
  public isContentEditable = false
  public width = 320
  public height = 200
  public focusCalls = 0
  public parent: EventTarget | null = null
  public readonly dataset: Record<string, string> = {}
  public readonly children: TestElement[] = []

  public constructor(
    public readonly ownerDocument: TestDocument,
    public readonly tagName: string,
  ) {
    super()
  }

  private disabledValue = false

  public get disabled(): boolean {
    return this.disabledValue
  }

  public set disabled(value: boolean) {
    this.disabledValue = value
    if (value && this.ownerDocument.activeElement === this) {
      this.ownerDocument.activeElement = this.ownerDocument.body
    }
  }

  public append(...children: TestElement[]): void {
    for (const child of children) child.parent = this
    this.children.push(...children)
  }

  public focus(): void {
    this.focusCalls += 1
    this.ownerDocument.activeElement = this
  }

  public getContext(kind: string): CanvasRenderingContext2D | null {
    if (kind !== '2d') return null
    return {
      clearRect() {}, beginPath() {}, moveTo() {}, lineTo() {}, stroke() {}, save() {}, restore() {},
    } as unknown as CanvasRenderingContext2D
  }

  public querySelector<ElementType extends Element>(selector: string): ElementType | null {
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

  public override dispatchEvent(event: Event): boolean {
    const dispatched = super.dispatchEvent(event)
    if (event.bubbles && !event.cancelBubble) this.parent?.dispatchEvent(event)
    return dispatched && !event.defaultPrevented
  }
}

class TestDocument extends EventTarget {
  public activeElement: TestElement | null = null
  public readonly body: TestElement
  public parent: EventTarget | null = null
  public pointerLockElement: Element | null = null
  public visibilityState: DocumentVisibilityState = 'visible'

  public constructor() {
    super()
    this.body = new TestElement(this, 'BODY')
    this.body.parent = this
  }

  public createElement(tagName: string): TestElement {
    return new TestElement(this, tagName.toUpperCase())
  }

  public exitPointerLock(): void {}

  public override dispatchEvent(event: Event): boolean {
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

function revisionWithRememberedFormula(): OrderCatalogRevision {
  const blank = diagramToJson(new DiagramBuilder().build())
  return decodeOrderCatalog([
    { id: 'first', prerequisites: [], reward: 2, goal: blank },
    {
      id: 'remembered',
      prerequisites: ['first'],
      reward: 7,
      goal: diagramToJson(formulaToDiagram('∀P:o. ¬P')),
      formula: '  ∀P:o. ¬P  ',
    },
  ])
}

type Deferred = {
  readonly promise: Promise<void>
  readonly resolve: () => void
  readonly reject: (error: Error) => void
}

function deferred(): Deferred {
  let resolve!: () => void
  let reject!: (error: Error) => void
  const promise = new Promise<void>((onResolve, onReject) => {
    resolve = onResolve
    reject = onReject
  })
  return { promise, resolve, reject }
}

function harness(initialRevision = revisionWithRememberedFormula()) {
  const windowTarget = new EventTarget()
  const documentTarget = new TestDocument()
  documentTarget.parent = windowTarget
  const root = element(documentTarget, 'orderEditor', 'section')
  root.hidden = true
  const title = element(documentTarget, 'orderEditorTitle', 'h2')
  const form = element(documentTarget, 'orderEditorForm', 'form')
  const id = element(documentTarget, 'orderEditorId', 'input')
  const prerequisites = element(documentTarget, 'orderEditorPrerequisites', 'textarea')
  const reward = element(documentTarget, 'orderEditorReward', 'input')
  const formula = element(documentTarget, 'orderEditorFormula', 'textarea')
  const preview = element(documentTarget, 'orderEditorPreview', 'canvas')
  const error = element(documentTarget, 'orderEditorError', 'p')
  const remove = element(documentTarget, 'orderEditorDelete', 'button')
  const cancel = element(documentTarget, 'orderEditorCancel', 'button')
  const save = element(documentTarget, 'orderEditorSave', 'button')
  form.append(id, prerequisites, reward, formula, preview, error, remove, cancel, save)
  root.append(title, form)
  documentTarget.body.append(root)

  const live = new LiveOrderCatalog(initialRevision)
  const saved: OrderCatalogRevision[] = []
  const deleted: string[] = []
  let saveResult: Promise<void> = Promise.resolve()
  let deleteResult: Promise<void> = Promise.resolve()
  const controller = mountOrderEditor(root as unknown as HTMLElement, {
    currentRevision: () => live.current,
    save: (candidate) => {
      saved.push(candidate)
      return saveResult
    },
    delete: (orderId) => {
      deleted.push(orderId)
      return deleteResult
    },
  })
  return {
    windowTarget, documentTarget, root, title, form, id, prerequisites, reward, formula, preview, error, remove, cancel, save,
    saved, deleted, controller, live,
    setSaveResult: (result: Promise<void>) => { saveResult = result },
    setDeleteResult: (result: Promise<void>) => { deleteResult = result },
  }
}

function submit(form: TestElement): Event {
  const event = new Event('submit', { bubbles: true, cancelable: true })
  form.dispatchEvent(event)
  return event
}

function click(target: TestElement): void {
  target.dispatchEvent(new Event('click', { bubbles: true, cancelable: true }))
}

function key(code: string, shiftKey = false): Event {
  return Object.defineProperties(new Event('keydown', { bubbles: true, cancelable: true }), {
    code: { value: code },
    shiftKey: { value: shiftKey },
  })
}

function attachGlobalInput(h: ReturnType<typeof harness>, pause: () => void) {
  return attachWorldInput(h.root as unknown as HTMLElement, {
    pointerDown: () => {},
    pointerUp: () => {},
    pointerCancel: () => {},
    category: () => {},
    toggleLedger: () => {},
    stepBack: () => {},
    toggleDeveloperMode: () => {},
    pause,
    engagementChanged: () => {},
  }, {
    window: h.windowTarget as Window,
    document: h.documentTarget as unknown as Document,
  })
}

async function settle(): Promise<void> {
  await Promise.resolve()
  await Promise.resolve()
}

describe('order editor controller', () => {
  it('shows an existing authoritative definition without making its ID editable', () => {
    // Catches edit mode inventing title authority, losing metadata, or deriving preview from formula text.
    const h = harness()
    const definition = revisionWithRememberedFormula().byId.get('remembered')!

    h.controller.edit(definition)

    expect(h.controller.isOpen).toBe(true)
    expect(h.title.textContent).toBe('Edit order')
    expect(h.id.value).toBe('remembered')
    expect(h.id.readOnly).toBe(true)
    expect(h.prerequisites.value).toBe('first')
    expect(h.reward.value).toBe('7')
    expect(h.formula.value).toBe('  ∀P:o. ¬P  ')
    expect(h.preview.dataset['diagramSnapshot']).toBe(definition.goal.json)
    expect(h.remove.hidden).toBe(false)
    expect(h.save.textContent).toBe('Save changes')
    expect(h.id.ownerDocument.activeElement).toBe(h.prerequisites)

    h.controller.edit(revisionWithRememberedFormula().byId.get('first')!)
    expect(h.formula.value).toBe('')
  })

  it('starts creation with a blank ID, one reward, no prerequisites, and an empty-sheet preview', () => {
    // Catches create mode inheriting edit state or invoking a runtime puzzle generator.
    const h = harness()
    const blankJson = JSON.stringify(diagramToJson(new DiagramBuilder().build()))

    h.controller.create()

    expect(h.title.textContent).toBe('Create order')
    expect(h.id.value).toBe('')
    expect(h.id.readOnly).toBe(false)
    expect(h.prerequisites.value).toBe('')
    expect(h.reward.value).toBe('1')
    expect(h.formula.value).toBe('')
    expect(h.preview.dataset['diagramSnapshot']).toBe(blankJson)
    expect(h.remove.hidden).toBe(true)
    expect(h.save.textContent).toBe('Create order')
    expect(h.id.ownerDocument.activeElement).toBe(h.id)
  })

  it('uses exact nonblank formula text to replace the goal in a decoded candidate revision', async () => {
    // Catches formula normalization or a mutated read-only control changing edit identity.
    const h = harness()
    h.controller.edit(revisionWithRememberedFormula().byId.get('remembered')!)
    h.id.value = 'forged-id'
    h.formula.value = '  ∀P:o. ¬¬P  '

    submit(h.form)
    await settle()

    const changed = h.saved[0]!.byId.get('remembered')!
    expect(h.saved[0]!.byId.has('forged-id')).toBe(false)
    expect(changed.formula).toBe('  ∀P:o. ¬¬P  ')
    expect(changed.goal.json).toBe(JSON.stringify(diagramToJson(formulaToDiagram('  ∀P:o. ¬¬P  '))))
    expect(changed.goal.json).not.toBe(revisionWithRememberedFormula().byId.get('remembered')!.goal.json)
  })

  it('clears remembered formula while retaining an existing authoritative diagram', async () => {
    // Catches blank formula replacing the diagram with an empty sheet or preserving stale formula authority.
    const initial = revisionWithRememberedFormula()
    const h = harness(initial)
    h.controller.edit(initial.byId.get('remembered')!)
    h.formula.value = ' \n '

    submit(h.form)
    await settle()

    const changed = h.saved[0]!.byId.get('remembered')!
    expect(changed.formula).toBeUndefined()
    expect(changed.goal.json).toBe(initial.byId.get('remembered')!.goal.json)
  })

  it('retains the blank diagram when a new order is submitted without a formula', async () => {
    // Catches blank creation passing through a puzzle generator or lacking a decoded catalog revision.
    const h = harness()
    h.controller.create()
    h.id.value = 'blank-new'

    submit(h.form)
    await settle()

    const created = h.saved[0]!.byId.get('blank-new')!
    expect(created.goal.json).toBe(JSON.stringify(diagramToJson(new DiagramBuilder().build())))
    expect(created.formula).toBeUndefined()
  })

  it('keeps parse and prerequisite-graph failures open without invoking persistence', async () => {
    // Catches invalid formulas or graph edges crossing the permanent-content boundary.
    const parse = harness()
    parse.controller.create()
    parse.id.value = 'broken-formula'
    parse.formula.value = '∀'
    submit(parse.form)
    await settle()
    expect(parse.saved).toEqual([])
    expect(parse.controller.isOpen).toBe(true)
    expect(parse.error.textContent).toContain('expected a binder name at line 1, column 2')

    const graph = harness()
    graph.controller.create()
    graph.id.value = 'broken-edge'
    graph.prerequisites.value = 'missing-order'
    submit(graph.form)
    await settle()
    expect(graph.saved).toEqual([])
    expect(graph.controller.isOpen).toBe(true)
    expect(graph.error.textContent).toContain("requires missing order 'missing-order'")
  })

  it('rejects blank and duplicate prerequisite entries before persistence', async () => {
    // Catches comma/newline parsing silently dropping malformed prerequisite entries.
    const blank = harness()
    blank.controller.create()
    blank.id.value = 'blank-edge'
    blank.prerequisites.value = 'first,,remembered'
    submit(blank.form)
    await settle()
    expect(blank.saved).toEqual([])
    expect(blank.error.textContent).toMatch(/blank prerequisite/i)

    const duplicate = harness()
    duplicate.controller.create()
    duplicate.id.value = 'duplicate-edge'
    duplicate.prerequisites.value = 'first, first'
    submit(duplicate.form)
    await settle()
    expect(duplicate.saved).toEqual([])
    expect(duplicate.error.textContent).toContain("duplicate prerequisite 'first'")
  })

  it('stays open, restores controls, and leaves the live revision untouched after persistence rejects', async () => {
    // Catches failed persistence retaining a candidate preview or stranding the modal in pending state.
    const initial = revisionWithRememberedFormula()
    const gate = deferred()
    const h = harness(initial)
    h.setSaveResult(gate.promise)
    h.controller.edit(initial.byId.get('remembered')!)
    h.reward.value = '9'
    h.formula.value = '  ∀P:o. ¬¬P  '

    submit(h.form)
    const candidatePreview = h.saved[0]!.byId.get('remembered')!.goal.json
    expect(h.preview.dataset['diagramSnapshot']).toBe(candidatePreview)
    expect(candidatePreview).not.toBe(initial.byId.get('remembered')!.goal.json)

    gate.reject(new Error('repository is read-only'))
    await settle()

    expect(h.controller.isOpen).toBe(true)
    expect(h.error.textContent).toContain('repository is read-only')
    expect(h.id.disabled).toBe(false)
    expect(h.preview.dataset['diagramSnapshot']).toBe(initial.byId.get('remembered')!.goal.json)
    expect(h.live.current).toBe(initial)
    expect(initial.byId.get('remembered')!.reward).toBe(7)
  })

  it('closes save and delete only after their persistence promises resolve', async () => {
    // Catches closing before permanent content success or delete bypassing local graph validation.
    const saveGate = deferred()
    const saving = harness()
    saving.setSaveResult(saveGate.promise.then(() => {
      saving.live.publish(saving.saved[0]!)
    }))
    saving.controller.edit(revisionWithRememberedFormula().byId.get('remembered')!)
    saving.formula.value = '  ∀P:o. ¬¬P  '
    submit(saving.form)
    const candidatePreview = saving.saved[0]!.byId.get('remembered')!.goal.json
    expect(saving.controller.isOpen).toBe(true)
    expect(saving.save.disabled).toBe(true)
    expect(saving.preview.dataset['diagramSnapshot']).toBe(candidatePreview)
    saveGate.resolve()
    await settle()
    expect(saving.controller.isOpen).toBe(false)
    expect(saving.preview.dataset['diagramSnapshot']).toBe(candidatePreview)
    expect(saving.live.current).toBe(saving.saved[0])

    const deleteGate = deferred()
    const deleting = harness()
    deleting.setDeleteResult(deleteGate.promise)
    deleting.controller.edit(revisionWithRememberedFormula().byId.get('remembered')!)
    click(deleting.remove)
    expect(deleting.deleted).toEqual(['remembered'])
    expect(deleting.controller.isOpen).toBe(true)
    expect(deleting.remove.disabled).toBe(true)
    deleteGate.resolve()
    await settle()
    expect(deleting.controller.isOpen).toBe(false)
  })

  it('traps focus while leaving Escape to global Pause without losing the draft', () => {
    const h = harness()
    let paused = false
    const input = attachGlobalInput(h, () => { paused = true })
    input.suspend()
    h.controller.create()

    h.id.dispatchEvent(key('Tab', true))
    expect(h.id.ownerDocument.activeElement).toBe(h.save)
    h.save.dispatchEvent(key('Tab'))
    expect(h.id.ownerDocument.activeElement).toBe(h.id)

    h.formula.value = 'draft formula'
    const escape = key('Escape')
    h.formula.dispatchEvent(escape)
    expect(paused).toBe(true)
    expect(h.controller.isOpen).toBe(true)
    expect(h.formula.value).toBe('draft formula')
    expect(escape.defaultPrevented).toBe(true)
    expect(escape.cancelBubble).toBe(false)

    input.resume()
    paused = false
    expect(paused).toBe(false)
    expect(h.controller.isOpen).toBe(true)
    expect(h.formula.value).toBe('draft formula')
  })

  it('routes pending Escape to global Pause after disabled focus falls back to the body', async () => {
    const gate = deferred()
    const h = harness()
    let paused = false
    const input = attachGlobalInput(h, () => { paused = true })
    input.suspend()
    h.setSaveResult(gate.promise)
    h.controller.edit(revisionWithRememberedFormula().byId.get('remembered')!)

    submit(h.form)
    expect(h.documentTarget.activeElement).toBe(h.documentTarget.body)
    const escape = key('Escape')
    h.documentTarget.body.dispatchEvent(escape)

    expect(h.controller.isOpen).toBe(true)
    expect(paused).toBe(true)
    expect(escape.defaultPrevented).toBe(true)
    expect(escape.cancelBubble).toBe(false)

    gate.resolve()
    await settle()
  })

  it('uses Backspace as editor step-back only outside editable text', () => {
    const outside = harness()
    outside.controller.create()
    outside.save.focus()
    const close = key('Backspace')
    outside.save.dispatchEvent(close)
    expect(outside.controller.isOpen).toBe(false)
    expect(close.defaultPrevented).toBe(true)
    expect(close.cancelBubble).toBe(true)

    for (const editable of ['input', 'textarea', 'contenteditable'] as const) {
      const h = harness()
      h.controller.create()
      const target = editable === 'input'
        ? h.id
        : editable === 'textarea'
          ? h.formula
          : h.documentTarget.createElement('div')
      if (editable === 'contenteditable') {
        target.isContentEditable = true
        h.form.append(target)
      }
      target.focus()
      target.value = 'draft text'
      const backspace = key('Backspace')
      target.dispatchEvent(backspace)

      expect(h.controller.isOpen).toBe(true)
      expect(target.value).toBe('draft text')
      expect(backspace.defaultPrevented).toBe(false)
      expect(backspace.cancelBubble).toBe(false)
    }
  })

  it('keeps Cancel as the explicit editor close action', () => {
    const h = harness()
    h.controller.create()
    h.formula.value = 'discard me'

    click(h.cancel)

    expect(h.controller.isOpen).toBe(false)
  })

  it('keeps persistence locked across hide and rejects overlapping reopen, save, and delete attempts', async () => {
    // Catches modal visibility or session generation releasing an unresolved persistence operation.
    const gate = deferred()
    const h = harness()
    h.setSaveResult(gate.promise)
    h.controller.edit(revisionWithRememberedFormula().byId.get('remembered')!)
    submit(h.form)

    h.controller.create()
    expect(h.id.value).toBe('remembered')
    click(h.remove)
    expect(h.deleted).toEqual([])

    h.controller.hide()
    expect(h.controller.isOpen).toBe(false)
    h.controller.create()
    submit(h.form)
    click(h.remove)
    expect(h.controller.isOpen).toBe(false)
    expect(h.saved).toHaveLength(1)
    expect(h.deleted).toEqual([])

    gate.resolve()
    await settle()

    h.controller.create()
    expect(h.controller.isOpen).toBe(true)
  })

  it('disposes every editor action listener', () => {
    // Catches a disposed controller continuing to save or reopen hidden UI.
    const h = harness()
    h.controller.create()
    h.id.value = 'disposed'
    h.controller.dispose()
    submit(h.form)
    click(h.remove)
    expect(h.saved).toEqual([])
    expect(h.deleted).toEqual([])
    expect(h.controller.isOpen).toBe(false)
  })
})
