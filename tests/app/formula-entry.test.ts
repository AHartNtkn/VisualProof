import { afterEach, beforeEach, describe, expect, it, vi } from 'vitest'
import { mountFormulaEntry } from '../../src/app/formula-entry'
import type { Diagram } from '../../src/kernel/diagram/diagram'

class TestElement extends EventTarget {
  readonly children: TestElement[] = []
  readonly attributes = new Map<string, string>()
  readonly ownerDocument: TestDocument
  parentElement: TestElement | null = null
  className = ''
  textContent = ''
  hidden = false
  value = ''
  type = ''
  id = ''
  htmlFor = ''
  required = false
  isConnected = true
  focusCalls = 0

  constructor(ownerDocument: TestDocument, readonly tagName: string) {
    super()
    this.ownerDocument = ownerDocument
  }

  append(...nodes: TestElement[]): void {
    for (const node of nodes) {
      node.parentElement = this
      this.children.push(node)
    }
  }

  remove(): void {
    if (this.parentElement === null) return
    const index = this.parentElement.children.indexOf(this)
    if (index >= 0) this.parentElement.children.splice(index, 1)
    this.parentElement = null
  }

  focus(): void {
    this.focusCalls += 1
    this.ownerDocument.activeElement = this
  }

  matches(selector: string): boolean { return selector === ':disabled' && this.required }

  setAttribute(name: string, value: string): void { this.attributes.set(name, value) }
  getAttribute(name: string): string | null { return this.attributes.get(name) ?? null }
  removeAttribute(name: string): void { this.attributes.delete(name) }

  querySelector(selector: string): TestElement | null {
    const matches = (element: TestElement): boolean => selector.startsWith('.')
      ? element.className.split(/\s+/u).includes(selector.slice(1))
      : element.tagName === selector.toLowerCase()
    for (const child of this.children) {
      if (matches(child)) return child
      const nested = child.querySelector(selector)
      if (nested !== null) return nested
    }
    return null
  }
}

class TestDocument {
  activeElement: TestElement | null = null

  createElement(tagName: string): TestElement { return new TestElement(this, tagName) }
}

let documentDouble!: TestDocument

beforeEach(() => {
  documentDouble = new TestDocument()
  vi.stubGlobal('document', documentDouble)
})

afterEach(() => { vi.unstubAllGlobals() })

function mounted(commit: (diagram: Diagram) => void) {
  const host = documentDouble.createElement('main')
  const opener = documentDouble.createElement('button')
  host.append(opener)
  const entry = mountFormulaEntry(host as unknown as HTMLElement, commit)
  const textarea = entry.root.querySelector('textarea') as unknown as TestElement
  const form = entry.root.querySelector('form') as unknown as TestElement
  const error = entry.root.querySelector('.vpa-formula-error') as unknown as TestElement
  const actions = entry.root.querySelector('.vpa-formula-actions') as unknown as TestElement
  const cancel = actions.children[1] as TestElement
  return { entry, opener, textarea, form, error, cancel }
}

describe('mountFormulaEntry', () => {
  it('commits a validated diagram and closes after a successful formula submission', () => {
    const commits: Diagram[] = []
    const { entry, opener, textarea, form } = mounted((diagram) => { commits.push(diagram) })

    entry.open(opener as unknown as HTMLElement)
    expect(documentDouble.activeElement).toBe(textarea)
    textarea.value = '∀ P : i → o. ∀ x : i. P(x)'
    form.dispatchEvent(new Event('submit', { cancelable: true }))

    expect(commits).toHaveLength(1)
    expect(Object.values(commits[0]!.nodes).filter((node) => node.kind === 'atom')).toHaveLength(1)
    expect(entry.root.hidden).toBe(true)
    expect(documentDouble.activeElement).toBe(opener)
  })

  it.each([
    ['Cancel', ({ cancel }: ReturnType<typeof mounted>) => cancel.dispatchEvent(new Event('click'))],
    ['Escape', ({ entry }: ReturnType<typeof mounted>) => {
      const event = new Event('keydown', { cancelable: true })
      Object.defineProperty(event, 'key', { value: 'Escape' })
      entry.root.dispatchEvent(event)
    }],
  ])('returns focus to the opener after %s', (_path, close) => {
    const { entry, opener, textarea, ...mountedEntry } = mounted(vi.fn<(diagram: Diagram) => void>())

    entry.open(opener as unknown as HTMLElement)
    expect(documentDouble.activeElement).toBe(textarea)
    close({ entry, opener, textarea, ...mountedEntry })

    expect(entry.root.hidden).toBe(true)
    expect(documentDouble.activeElement).toBe(opener)
  })

  it('does not resurrect opener focus on mode deactivation or disposal', () => {
    const { entry, opener, textarea } = mounted(vi.fn<(diagram: Diagram) => void>())

    entry.open(opener as unknown as HTMLElement)
    entry.deactivate()

    expect(opener.focusCalls).toBe(0)
    expect(documentDouble.activeElement).toBe(textarea)

    entry.open(opener as unknown as HTMLElement)
    entry.dispose()

    expect(opener.focusCalls).toBe(0)
  })

  it('keeps an invalid formula open, reports its location, and clears the field error on input', () => {
    const commit = vi.fn<(diagram: Diagram) => void>()
    const { entry, opener, textarea, form, error } = mounted(commit)

    entry.open(opener as unknown as HTMLElement)
    textarea.value = '∀ x. Missing(x)'
    form.dispatchEvent(new Event('submit', { cancelable: true }))

    expect(error.textContent).toMatch(/line 1, column \d+/u)
    expect(textarea.getAttribute('aria-invalid')).toBe('true')
    expect(entry.root.hidden).toBe(false)
    expect(commit).not.toHaveBeenCalled()

    textarea.dispatchEvent(new Event('input'))

    expect(error.textContent).toBe('')
    expect(textarea.getAttribute('aria-invalid')).toBeNull()
  })

  it('routes empty source through the formula parser rather than committing', () => {
    const commit = vi.fn<(diagram: Diagram) => void>()
    const { entry, opener, textarea, form, error } = mounted(commit)

    entry.open(opener as unknown as HTMLElement)
    form.dispatchEvent(new Event('submit', { cancelable: true }))

    expect(error.textContent).toMatch(/line 1, column \d+/u)
    expect(textarea.getAttribute('aria-invalid')).toBe('true')
    expect(entry.root.hidden).toBe(false)
    expect(commit).not.toHaveBeenCalled()
  })
})
