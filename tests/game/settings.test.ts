import { describe, expect, it } from 'vitest'
import { mountSettings } from '../../game/settings'

class TestElement extends EventTarget {
  hidden = true
  checked = false
  focusCalls = 0
  parent: TestElement | null = null
  readonly dataset: Record<string, string> = {}
  readonly children: TestElement[] = []

  constructor(readonly ownerDocument: { activeElement: TestElement | null }) {
    super()
  }

  append(...children: TestElement[]): void {
    for (const child of children) child.parent = this
    this.children.push(...children)
  }

  focus(): void {
    this.focusCalls += 1
    this.ownerDocument.activeElement = this
  }

  querySelector<T extends Element>(selector: string): T | null {
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

  override dispatchEvent(event: Event): boolean {
    const result = super.dispatchEvent(event)
    if (event.bubbles && !event.cancelBubble) this.parent?.dispatchEvent(event)
    return result && !event.defaultPrevented
  }
}

function key(code: string, shiftKey = false): Event {
  return Object.defineProperties(new Event('keydown', { bubbles: true, cancelable: true }), {
    code: { value: code },
    shiftKey: { value: shiftKey },
  })
}

function harness() {
  const documentTarget = { activeElement: null as TestElement | null }
  const root = new TestElement(documentTarget)
  root.dataset['settings'] = ''
  const tutorials = new TestElement(documentTarget)
  tutorials.dataset['settingsTutorials'] = ''
  const developerTools = new TestElement(documentTarget)
  developerTools.dataset['settingsDeveloperTools'] = ''
  const back = new TestElement(documentTarget)
  back.dataset['settingsBack'] = ''
  root.append(tutorials, developerTools, back)
  const calls: string[] = []
  const controller = mountSettings(root as unknown as HTMLElement, {
    setTutorialsEnabled: (enabled) => calls.push(`tutorials:${enabled}`),
    setDeveloperToolsEnabled: (enabled) => calls.push(`developer-tools:${enabled}`),
    back: () => calls.push('back'),
  })
  return { root, tutorials, developerTools, back, calls, controller }
}

describe('settings controller', () => {
  it('shows each independent setting and reports only the checkbox that changed', () => {
    // Catches per-save Tutorials and application Developer Tools becoming one authority.
    const settings = harness()
    settings.controller.show({ tutorialsEnabled: true, developerToolsEnabled: false })

    expect(settings.root.hidden).toBe(false)
    expect(settings.tutorials.checked).toBe(true)
    expect(settings.developerTools.checked).toBe(false)
    expect(settings.tutorials.ownerDocument.activeElement).toBe(settings.tutorials)

    settings.tutorials.checked = false
    settings.tutorials.dispatchEvent(new Event('change'))
    settings.developerTools.checked = true
    settings.developerTools.dispatchEvent(new Event('change'))

    expect(settings.calls).toEqual(['tutorials:false', 'developer-tools:true'])
  })

  it('traps focus and returns to Pause on Escape', () => {
    // Catches modal keyboard focus escaping into world controls or Escape reaching world input.
    const settings = harness()
    settings.controller.show({ tutorialsEnabled: true, developerToolsEnabled: false })

    settings.tutorials.dispatchEvent(key('Tab'))
    expect(settings.tutorials.ownerDocument.activeElement).toBe(settings.developerTools)
    settings.developerTools.dispatchEvent(key('Tab'))
    expect(settings.tutorials.ownerDocument.activeElement).toBe(settings.back)
    settings.back.dispatchEvent(key('Tab'))
    expect(settings.tutorials.ownerDocument.activeElement).toBe(settings.tutorials)
    settings.tutorials.dispatchEvent(key('Tab', true))
    expect(settings.tutorials.ownerDocument.activeElement).toBe(settings.back)

    const escape = key('Escape')
    settings.back.dispatchEvent(escape)

    expect(settings.root.hidden).toBe(true)
    expect(settings.calls).toEqual(['back'])
    expect(escape.defaultPrevented).toBe(true)
    expect(escape.cancelBubble).toBe(true)
  })
})
