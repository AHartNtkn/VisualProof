import { describe, expect, it } from 'vitest'
import { mountPauseMenu } from '../../game/pause'

class TestElement extends EventTarget {
  public hidden = true
  public disabled = false
  public textContent = ''
  public focusCalls = 0
  public parent: TestElement | null = null
  public readonly dataset: Record<string, string> = {}
  public readonly children: TestElement[] = []

  public constructor(public readonly ownerDocument: { activeElement: TestElement | null }) {
    super()
  }

  public append(...children: TestElement[]): void {
    for (const child of children) child.parent = this
    this.children.push(...children)
  }

  public focus(): void {
    this.focusCalls += 1
    this.ownerDocument.activeElement = this
  }

  public querySelector<T extends Element>(selector: string): T | null {
    const key = selector.match(/^\[data-([a-z0-9-]+)\]$/)?.[1]
    if (key === undefined) throw new Error(`unsupported selector '${selector}'`)
    const datasetKey = key.replace(/-([a-z])/g, (_whole, letter: string) => letter.toUpperCase())
    if (Object.hasOwn(this.dataset, datasetKey)) return this as unknown as T
    for (const child of this.children) {
      const found = child.querySelector<T>(selector)
      if (found !== null) return found
    }
    return null
  }

  public override dispatchEvent(event: Event): boolean {
    const result = super.dispatchEvent(event)
    if (event.bubbles && !event.cancelBubble) this.parent?.dispatchEvent(event)
    return result && !event.defaultPrevented
  }
}

function element(documentTarget: { activeElement: TestElement | null }, name?: string): TestElement {
  const result = new TestElement(documentTarget)
  if (name !== undefined) result.dataset[name] = ''
  return result
}

function key(code: string): Event {
  return Object.defineProperty(new Event('keydown', { bubbles: true, cancelable: true }), 'code', { value: code })
}

function harness(actions: {
  resume?: () => void
  mainMenu?: () => Promise<void>
  quit?: () => Promise<void>
} = {}) {
  const documentTarget: { activeElement: TestElement | null } = { activeElement: null }
  const root = element(documentTarget, 'pause')
  const name = element(documentTarget, 'pauseWorldName')
  const error = element(documentTarget, 'pauseError')
  const resume = element(documentTarget, 'pauseResume')
  const mainMenu = element(documentTarget, 'pauseMainMenu')
  const quit = element(documentTarget, 'pauseQuit')
  root.append(name, error, resume, mainMenu, quit)
  const controller = mountPauseMenu(root as unknown as HTMLElement, {
    resume: actions.resume ?? (() => {}),
    mainMenu: actions.mainMenu ?? (() => Promise.resolve()),
    quit: actions.quit ?? (() => Promise.resolve()),
  })
  return { root, name, error, resume, mainMenu, quit, controller }
}

describe('pause menu', () => {
  it('opens as a focused modal and Escape resumes', () => {
    let resumes = 0
    const pause = harness({ resume: () => { resumes += 1 } })

    pause.controller.show('My Orchard')
    const escape = key('Escape')
    pause.resume.dispatchEvent(escape)

    expect(pause.root.hidden).toBe(false)
    expect(pause.name.textContent).toBe('My Orchard')
    expect(pause.resume.focusCalls).toBe(1)
    expect(resumes).toBe(1)
    expect(escape.defaultPrevented).toBe(true)
  })

  it('keeps keyboard focus within the pause actions', () => {
    const pause = harness()
    pause.controller.show('My Orchard')

    pause.resume.dispatchEvent(key('Tab'))
    expect(pause.mainMenu.ownerDocument.activeElement).toBe(pause.mainMenu)

    const backward = Object.defineProperty(key('Tab'), 'shiftKey', { value: true })
    pause.mainMenu.dispatchEvent(backward)
    expect(pause.resume.ownerDocument.activeElement).toBe(pause.resume)
  })

  it('stays open and restores controls when returning to the menu cannot save', async () => {
    const pause = harness({ mainMenu: () => Promise.reject(new Error('disk full')) })
    pause.controller.show('My Orchard')

    pause.mainMenu.dispatchEvent(new Event('click'))
    await Promise.resolve()
    await Promise.resolve()

    expect(pause.root.hidden).toBe(false)
    expect(pause.error.textContent).toBe('Could not return to main menu: disk full')
    expect(pause.resume.disabled).toBe(false)
    expect(pause.mainMenu.disabled).toBe(false)
    expect(pause.quit.disabled).toBe(false)
  })

  it('runs quit once while its save barrier is pending', async () => {
    let resolve!: () => void
    const pending = new Promise<void>((done) => { resolve = done })
    let quits = 0
    const pause = harness({ quit: () => { quits += 1; return pending } })
    pause.controller.show('My Orchard')

    pause.quit.dispatchEvent(new Event('click'))
    pause.quit.dispatchEvent(new Event('click'))

    expect(quits).toBe(1)
    expect(pause.resume.disabled).toBe(true)
    resolve()
    await pending
  })
})
