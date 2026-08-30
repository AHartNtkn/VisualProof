import { describe, expect, it } from 'vitest'
import { attachWorldInput } from '../../game/input'
import { applyDeveloperToolsSetting, mountSettings } from '../../game/settings'
import { mountTutorialCard } from '../../game/tutorial-card'
import { mountTutorialEditor } from '../../game/tutorial-editor'
import { WorldStateController } from '../../game/world-state'
import { initialCameraState } from '../../src/game/camera'
import { ToolInventory } from '../../src/game/tools'
import {
  decodeTutorialContent,
  LiveTutorialContent,
  openingTutorialContent,
  type TutorialContentRevision,
} from '../../src/game/tutorial/content'

class TestElement extends EventTarget {
  hidden = false
  value = ''
  textContent = ''
  className = ''
  readOnly = false
  isContentEditable = false
  tabIndex = -1
  checked = false
  parent: EventTarget | null = null
  readonly dataset: Record<string, string> = {}
  readonly children: TestElement[] = []
  readonly attributes = new Map<string, string>()

  constructor(readonly ownerDocument: TestDocument, readonly tagName: string) { super() }

  private disabledValue = false

  get disabled(): boolean { return this.disabledValue }

  set disabled(value: boolean) {
    this.disabledValue = value
    if (value && this.ownerDocument.activeElement === this) {
      this.ownerDocument.activeElement = this.ownerDocument.body
    }
  }

  append(...children: TestElement[]): void {
    for (const child of children) child.parent = this
    this.children.push(...children)
  }

  appendChild(child: TestElement): TestElement {
    this.append(child)
    return child
  }

  replaceChildren(...children: TestElement[]): void {
    this.children.splice(0, this.children.length)
    this.append(...children)
  }

  contains(target: EventTarget | null): boolean {
    return target === this || this.children.some((child) => child.contains(target))
  }

  focus(): void {
    this.ownerDocument.activeElement = this
  }

  setAttribute(name: string, value: string): void {
    this.attributes.set(name, value)
  }

  removeAttribute(name: string): void {
    this.attributes.delete(name)
  }

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
    if (!Object.hasOwn(event, 'composedPath')) {
      Object.defineProperty(event, 'composedPath', { value: () => [this] })
    }
    const dispatched = super.dispatchEvent(event)
    if (event.bubbles && !event.cancelBubble) this.parent?.dispatchEvent(event)
    return dispatched && !event.defaultPrevented
  }
}

class TestDocument extends EventTarget {
  activeElement: TestElement | null = null
  readonly body: TestElement
  parent: EventTarget | null = null
  pointerLockElement: Element | null = null
  visibilityState: DocumentVisibilityState = 'visible'

  constructor() {
    super()
    this.body = new TestElement(this, 'BODY')
    this.body.parent = this
  }

  createElement(tagName: string): TestElement {
    return new TestElement(this, tagName.toUpperCase())
  }

  exitPointerLock(): void {}

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

function revisionWithMove(text = 'Use W to move.'): TutorialContentRevision {
  return decodeTutorialContent(openingTutorialContent.current.definitions.map((definition) => ({
    ...definition,
    text: definition.milestoneId === 'move' ? text : definition.text,
  })))
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

function harness(initial = revisionWithMove()) {
  const windowTarget = new EventTarget()
  const documentTarget = new TestDocument()
  documentTarget.parent = windowTarget
  const root = element(documentTarget, 'tutorialEditor', 'section')
  root.hidden = true
  const form = element(documentTarget, 'tutorialEditorForm', 'form')
  const id = element(documentTarget, 'tutorialEditorId', 'input')
  const text = element(documentTarget, 'tutorialEditorText', 'textarea')
  const error = element(documentTarget, 'tutorialEditorError', 'p')
  const cancel = element(documentTarget, 'tutorialEditorCancel', 'button')
  const save = element(documentTarget, 'tutorialEditorSave', 'button')
  form.append(id, text, error, cancel, save)
  root.append(form)
  documentTarget.body.append(root)

  const live = new LiveTutorialContent(initial)
  const saved: TutorialContentRevision[] = []
  let saveResult: Promise<void> = Promise.resolve()
  let foreground = true
  const controller = mountTutorialEditor(root as unknown as HTMLElement, {
    currentRevision: () => live.current,
    isForeground: () => foreground,
    save: async (candidate) => {
      saved.push(candidate)
      await saveResult
      live.publish(candidate)
    },
  })
  return {
    windowTarget, documentTarget, root, form, id, text, error, cancel, save,
    live, saved, controller,
    setSaveResult: (result: Promise<void>) => { saveResult = result },
    setForeground: (value: boolean) => { foreground = value },
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
    pointerDown: () => {}, pointerUp: () => {}, pointerCancel: () => {}, category: () => {},
    toggleLedger: () => {}, stepBack: () => {}, toggleDeveloperMode: () => {}, pause,
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

describe('tutorial editor controller', () => {
  it('shows immutable milestone context and publishes a complete edited revision', async () => {
    // Catches editing prose by detached overlay or changing semantic milestone identity.
    const h = harness()
    h.controller.edit(h.live.current.definition('move'))

    expect(h.controller.isOpen).toBe(true)
    expect(h.id.value).toBe('move')
    expect(h.id.readOnly).toBe(true)
    expect(h.text.value).toBe('Use W to move.')
    expect(h.documentTarget.activeElement).toBe(h.text)

    h.text.value = 'Use W/A/S/D to move.'
    submit(h.form)
    await settle()

    expect(h.saved).toHaveLength(1)
    expect(h.saved[0]?.definitions).toHaveLength(h.live.current.definitions.length)
    expect(h.saved[0]?.definition('move').text).toBe('Use W/A/S/D to move.')
    expect(h.controller.isOpen).toBe(false)
    expect(h.live.current).toBe(h.saved[0])
  })

  it('rejects blank text locally and leaves the draft visible', async () => {
    // Catches invalid authored copy reaching permanent publication or closing the recovery surface.
    const h = harness()
    h.controller.edit(h.live.current.definition('move'))
    h.text.value = '   '
    submit(h.form)
    await settle()

    expect(h.saved).toEqual([])
    expect(h.controller.isOpen).toBe(true)
    expect(h.text.value).toBe('   ')
    expect(h.error.textContent).toMatch(/non-blank/i)
  })

  it('keeps the draft and prior live copy after permanent publication rejects', async () => {
    // Catches a failed durable write publishing live copy, discarding recovery text, or stranding controls.
    const initial = revisionWithMove()
    const gate = deferred()
    const h = harness(initial)
    h.setSaveResult(gate.promise)
    h.controller.edit(initial.definition('move'))
    h.text.value = 'My unsaved movement draft.'
    submit(h.form)
    expect(h.save.disabled).toBe(true)

    gate.reject(new Error('repository is read-only'))
    await settle()

    expect(h.controller.isOpen).toBe(true)
    expect(h.text.value).toBe('My unsaved movement draft.')
    expect(h.error.textContent).toContain('repository is read-only')
    expect(h.save.disabled).toBe(false)
    expect(h.live.current).toBe(initial)
    expect(h.live.current.definition('move').text).toBe('Use W to move.')
  })

  it('refreshes the live tutorial card only after publication succeeds', async () => {
    // Catches the visible instruction getting ahead of the durable authored revision.
    const h = harness()
    const cardRoot = new TestElement(h.documentTarget, 'ASIDE')
    const card = mountTutorialCard(cardRoot as unknown as HTMLElement, { edit: () => {} })
    const renderCurrent = () => card.render({
      milestoneId: 'move',
      text: h.live.current.definition('move').text,
    }, true, true)
    renderCurrent()
    expect(cardRoot.querySelector<HTMLElement>('[data-tutorial-instruction]')?.textContent)
      .toBe('Use W to move.')

    h.controller.edit(h.live.current.definition('move'))
    h.text.value = 'Move with all four direction keys.'
    submit(h.form)
    await settle()
    renderCurrent()

    expect(cardRoot.querySelector<HTMLElement>('[data-tutorial-instruction]')?.textContent)
      .toBe('Move with all four direction keys.')
  })

  it('uses Backspace as close only outside editable text while the editor is foreground', () => {
    // Catches text editing or a background editor leaking Backspace into the wrong owner.
    const editable = harness()
    editable.controller.edit(editable.live.current.definition('move'))
    editable.text.value = 'draft text'
    const textBackspace = key('Backspace')
    editable.text.dispatchEvent(textBackspace)
    expect(editable.controller.isOpen).toBe(true)
    expect(editable.text.value).toBe('draft text')
    expect(textBackspace.defaultPrevented).toBe(false)

    editable.save.focus()
    const close = key('Backspace')
    editable.save.dispatchEvent(close)
    expect(editable.controller.isOpen).toBe(false)
    expect(close.defaultPrevented).toBe(true)
    expect(close.cancelBubble).toBe(true)

    const background = harness()
    background.controller.edit(background.live.current.definition('move'))
    background.text.value = 'draft behind Pause'
    background.setForeground(false)
    background.documentTarget.activeElement = background.documentTarget.body
    const backgroundBackspace = key('Backspace')
    background.documentTarget.body.dispatchEvent(backgroundBackspace)
    expect(background.controller.isOpen).toBe(true)
    expect(background.text.value).toBe('draft behind Pause')
    expect(backgroundBackspace.defaultPrevented).toBe(false)
  })

  it('keeps Backspace in the textarea when Pause left document focus stale', () => {
    // Catches Resume-era document focus lag making a textarea edit close the foreground editor.
    const h = harness()
    h.controller.edit(h.live.current.definition('move'))
    h.text.value = 'draft after Resume'
    h.documentTarget.activeElement = h.documentTarget.body

    const backspace = key('Backspace')
    h.text.dispatchEvent(backspace)

    expect(h.controller.isOpen).toBe(true)
    expect(h.text.value).toBe('draft after Resume')
    expect(backspace.defaultPrevented).toBe(false)
  })

  it('leaves Escape to Pause and preserves the draft through Resume', () => {
    // Catches the editor consuming Escape, unmounting behind Pause, or losing its draft on Resume.
    const h = harness()
    let paused = false
    const input = attachGlobalInput(h, () => { paused = true })
    input.suspend()
    h.controller.edit(h.live.current.definition('move'))
    h.text.value = 'draft behind Pause'

    const escape = key('Escape')
    h.text.dispatchEvent(escape)
    expect(paused).toBe(true)
    expect(escape.defaultPrevented).toBe(true)
    expect(escape.cancelBubble).toBe(false)
    expect(h.controller.isOpen).toBe(true)
    expect(h.text.value).toBe('draft behind Pause')

    input.resume()
    paused = false
    expect(paused).toBe(false)
    expect(h.controller.isOpen).toBe(true)
    expect(h.text.value).toBe('draft behind Pause')
  })

  it('closes on Cancel without publishing', () => {
    // Catches Cancel publishing a draft or leaving the editor visible.
    const h = harness()
    h.controller.edit(h.live.current.definition('move'))
    h.text.value = 'discarded'
    click(h.cancel)
    expect(h.controller.isOpen).toBe(false)
    expect(h.saved).toEqual([])

  })

  it('applies Settings shutdown across editor, card, foreground, and Pause ownership', () => {
    // Catches the actual Settings transition leaving any privileged surface or suspended owner stale.
    const h = harness()
    let developerMode = true
    let foreground: 'closed' | 'tutorial' = 'tutorial'
    let pauseVisible = false
    const inputCalls: string[] = []
    const cardRoot = new TestElement(h.documentTarget, 'ASIDE')
    const card = mountTutorialCard(cardRoot as unknown as HTMLElement, { edit: () => {} })
    const renderCard = () => card.render({ milestoneId: 'move', text: 'Use W to move.' }, true, developerMode)
    renderCard()
    h.controller.edit(h.live.current.definition('move'))
    expect(cardRoot.dataset['tutorialEditable']).toBe('true')
    expect(h.controller.isOpen).toBe(true)
    expect(foreground).toBe('tutorial')

    const camera = initialCameraState({ position: { x: 0, y: 1.7, z: 8 }, yaw: 0, pitch: 0 })
    const world = new WorldStateController({
      getCamera: () => camera,
      setCamera: () => {},
      tools: new ToolInventory(new Set(['sprout-spawner'])),
      ledger: { isOpen: false },
      foreground: { get isOpen() { return foreground !== 'closed' } },
      input: {
        suspend: () => { inputCalls.push('suspend') },
        resume: () => { inputCalls.push('resume') },
        engage: () => { inputCalls.push('engage'); return Promise.resolve() },
      },
      pauseMenu: {
        show: () => { pauseVisible = true },
        hide: () => { pauseVisible = false },
      },
      worldName: () => 'My Orchard',
      setFreeActive: () => {},
      cuttingCleared: () => {},
      stateChanged: () => {},
    })
    world.pause()

    const settingsRoot = element(h.documentTarget, 'settings', 'section')
    settingsRoot.hidden = true
    const tutorials = element(h.documentTarget, 'settingsTutorials', 'input')
    const developerTools = element(h.documentTarget, 'settingsDeveloperTools', 'input')
    const back = element(h.documentTarget, 'settingsBack', 'button')
    settingsRoot.append(tutorials, developerTools, back)
    const transitionCalls: string[] = []
    const settings = mountSettings(settingsRoot as unknown as HTMLElement, {
      setTutorialsEnabled: () => {},
      setDeveloperToolsEnabled: (enabled) => applyDeveloperToolsSetting(enabled, {
        persist: (value) => { transitionCalls.push(`persist:${value}`) },
        setDeveloperMode: (value) => { developerMode = value },
        hideForegroundEditors: () => {
          transitionCalls.push('hide-foreground')
          h.controller.hide()
        },
        clearForegroundEditor: () => { foreground = 'closed' },
        renderTutorial: renderCard,
        refreshVisibleLedger: () => { transitionCalls.push('refresh-ledger') },
        mirrorRuntimeState: () => { transitionCalls.push('mirror-runtime') },
      }),
      back: () => {},
    })
    settings.show({ tutorialsEnabled: true, developerToolsEnabled: true })
    developerTools.checked = false
    developerTools.dispatchEvent(new Event('change'))

    expect(developerMode).toBe(false)
    expect(h.controller.isOpen).toBe(false)
    expect(foreground).toBe('closed')
    expect(cardRoot.dataset['tutorialEditable']).toBeUndefined()
    expect(world.isPaused).toBe(true)
    expect(pauseVisible).toBe(true)
    expect(transitionCalls).toEqual([
      'persist:false', 'hide-foreground', 'refresh-ledger', 'mirror-runtime',
    ])

    world.resume()
    expect(world.isPaused).toBe(false)
    expect(pauseVisible).toBe(false)
    expect(inputCalls).toEqual(['suspend', 'resume', 'engage'])
  })
})
